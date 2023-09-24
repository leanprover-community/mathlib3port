/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Data.FunLike.Embedding
import Data.Prod.Pprod
import Data.Sigma.Basic
import Data.Option.Basic
import Data.Subtype
import Logic.Equiv.Basic

#align_import logic.embedding.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Injective functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v w x

namespace Function

#print Function.Embedding /-
-- depending on cardinalities, an injective function may not exist
/-- `α ↪ β` is a bundled injective function. -/
@[nolint has_nonempty_instance]
structure Embedding (α : Sort _) (β : Sort _) where
  toFun : α → β
  inj' : Injective to_fun
#align function.embedding Function.Embedding
-/

infixr:25 " ↪ " => Embedding

instance {α : Sort u} {β : Sort v} : CoeFun (α ↪ β) fun _ => α → β :=
  ⟨Embedding.toFun⟩

initialize_simps_projections Embedding (toFun → apply)

instance {α : Sort u} {β : Sort v} : EmbeddingLike (α ↪ β) α β
    where
  coe := Embedding.toFun
  injective' := Embedding.inj'
  coe_injective' f g h := by cases f; cases g; congr

instance {α β : Sort _} : CanLift (α → β) (α ↪ β) coeFn Injective where prf f hf := ⟨⟨f, hf⟩, rfl⟩

end Function

section Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

#print Equiv.toEmbedding /-
/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `equiv.coe_embedding`.
The explicit `equiv.to_embedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f.to_embedding = s.map f := by simp
-- Error, `f` has type `fin 3 ≃ fin 3` but is expected to have type `fin 3 ↪ ?m_1 : Type ?`
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f = s.map f.to_embedding := by simp
```
-/
protected def Equiv.toEmbedding : α ↪ β :=
  ⟨f, f.Injective⟩
#align equiv.to_embedding Equiv.toEmbedding
-/

#print Equiv.coe_toEmbedding /-
@[simp]
theorem Equiv.coe_toEmbedding : ⇑f.toEmbedding = f :=
  rfl
#align equiv.coe_to_embedding Equiv.coe_toEmbedding
-/

#print Equiv.toEmbedding_apply /-
theorem Equiv.toEmbedding_apply (a : α) : f.toEmbedding a = f a :=
  rfl
#align equiv.to_embedding_apply Equiv.toEmbedding_apply
-/

#print Equiv.coeEmbedding /-
instance Equiv.coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equiv.toEmbedding⟩
#align equiv.coe_embedding Equiv.coeEmbedding
-/

#print Equiv.Perm.coeEmbedding /-
@[reducible]
instance Equiv.Perm.coeEmbedding : Coe (Equiv.Perm α) (α ↪ α) :=
  Equiv.coeEmbedding
#align equiv.perm.coe_embedding Equiv.Perm.coeEmbedding
-/

@[simp]
theorem Equiv.coe_eq_toEmbedding : ↑f = f.toEmbedding :=
  rfl
#align equiv.coe_eq_to_embedding Equiv.coe_eq_toEmbedding

#print Equiv.asEmbedding /-
/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps]
def Equiv.asEmbedding {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  ⟨coe ∘ e, Subtype.coe_injective.comp e.Injective⟩
#align equiv.as_embedding Equiv.asEmbedding
-/

end Equiv

namespace Function

namespace Embedding

#print Function.Embedding.coe_injective /-
theorem coe_injective {α β} : @Function.Injective (α ↪ β) (α → β) coeFn :=
  FunLike.coe_injective
#align function.embedding.coe_injective Function.Embedding.coe_injective
-/

#print Function.Embedding.ext /-
@[ext]
theorem ext {α β} {f g : Embedding α β} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align function.embedding.ext Function.Embedding.ext
-/

#print Function.Embedding.ext_iff /-
theorem ext_iff {α β} {f g : Embedding α β} : (∀ x, f x = g x) ↔ f = g :=
  FunLike.ext_iff.symm
#align function.embedding.ext_iff Function.Embedding.ext_iff
-/

#print Function.Embedding.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {α β} (f : α ↪ β) : toFun f = f :=
  rfl
#align function.embedding.to_fun_eq_coe Function.Embedding.toFun_eq_coe
-/

#print Function.Embedding.coeFn_mk /-
@[simp]
theorem coeFn_mk {α β} (f : α → β) (i) : (@mk _ _ f i : α → β) = f :=
  rfl
#align function.embedding.coe_fn_mk Function.Embedding.coeFn_mk
-/

#print Function.Embedding.mk_coe /-
@[simp]
theorem mk_coe {α β : Type _} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f := by ext; simp
#align function.embedding.mk_coe Function.Embedding.mk_coe
-/

#print Function.Embedding.injective /-
protected theorem injective {α β} (f : α ↪ β) : Injective f :=
  EmbeddingLike.injective f
#align function.embedding.injective Function.Embedding.injective
-/

#print Function.Embedding.apply_eq_iff_eq /-
theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f
#align function.embedding.apply_eq_iff_eq Function.Embedding.apply_eq_iff_eq
-/

#print Function.Embedding.refl /-
/-- The identity map as a `function.embedding`. -/
@[refl, simps (config := { simpRhs := true })]
protected def refl (α : Sort _) : α ↪ α :=
  ⟨id, injective_id⟩
#align function.embedding.refl Function.Embedding.refl
-/

#print Function.Embedding.trans /-
/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps (config := { simpRhs := true })]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.Injective.comp f.Injective⟩
#align function.embedding.trans Function.Embedding.trans
-/

#print Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding /-
@[simp]
theorem equiv_toEmbedding_trans_symm_toEmbedding {α β : Sort _} (e : α ≃ β) :
    e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _ := by ext; simp
#align function.embedding.equiv_to_embedding_trans_symm_to_embedding Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding
-/

#print Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding /-
@[simp]
theorem equiv_symm_toEmbedding_trans_toEmbedding {α β : Sort _} (e : α ≃ β) :
    e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _ := by ext; simp
#align function.embedding.equiv_symm_to_embedding_trans_to_embedding Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding
-/

#print Function.Embedding.congr /-
/-- Transfer an embedding along a pair of equivalences. -/
@[simps (config := { fullyApplied := false })]
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α ↪ γ) : β ↪ δ :=
  (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)
#align function.embedding.congr Function.Embedding.congr
-/

#print Function.Embedding.ofSurjective /-
/-- A right inverse `surj_inv` of a surjective function as an `embedding`. -/
protected noncomputable def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩
#align function.embedding.of_surjective Function.Embedding.ofSurjective
-/

#print Function.Embedding.equivOfSurjective /-
/-- Convert a surjective `embedding` to an `equiv` -/
protected noncomputable def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equiv.ofBijective f ⟨f.Injective, hf⟩
#align function.embedding.equiv_of_surjective Function.Embedding.equivOfSurjective
-/

#print Function.Embedding.ofIsEmpty /-
/-- There is always an embedding from an empty type. -/
protected def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩
#align function.embedding.of_is_empty Function.Embedding.ofIsEmpty
-/

#print Function.Embedding.setValue /-
/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def setValue {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a',
    by
    intro x y h
    dsimp at h 
    split_ifs at h  <;> try subst b <;> try simp only [f.injective.eq_iff] at * <;> cc⟩
#align function.embedding.set_value Function.Embedding.setValue
-/

#print Function.Embedding.setValue_eq /-
theorem setValue_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a = b := by simp [set_value]
#align function.embedding.set_value_eq Function.Embedding.setValue_eq
-/

#print Function.Embedding.some /-
/-- Embedding into `option α` using `some`. -/
@[simps (config := { fullyApplied := false })]
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩
#align function.embedding.some Function.Embedding.some
-/

/- warning: function.embedding.coe_option clashes with function.embedding.some -> Function.Embedding.some
Case conversion may be inaccurate. Consider using '#align function.embedding.coe_option Function.Embedding.someₓ'. -/
#print Function.Embedding.some /-
/-- Embedding into `option α` using `coe`. Usually the correct synctatical form for `simp`. -/
@[simps (config := { fullyApplied := false })]
def some {α} : α ↪ Option α :=
  ⟨coe, Option.some_injective α⟩
#align function.embedding.coe_option Function.Embedding.some
-/

#print Function.Embedding.optionMap /-
/-- A version of `option.map` for `function.embedding`s. -/
@[simps (config := { fullyApplied := false })]
def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.Injective⟩
#align function.embedding.option_map Function.Embedding.optionMap
-/

#print Function.Embedding.subtype /-
/-- Embedding of a `subtype`. -/
def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨coe, fun _ _ => Subtype.ext_val⟩
#align function.embedding.subtype Function.Embedding.subtype
-/

#print Function.Embedding.coe_subtype /-
@[simp]
theorem coe_subtype {α} (p : α → Prop) : ⇑(subtype p) = coe :=
  rfl
#align function.embedding.coe_subtype Function.Embedding.coe_subtype
-/

#print Function.Embedding.quotientOut /-
/-- `quotient.out` as an embedding. -/
noncomputable def quotientOut (α) [s : Setoid α] : Quotient s ↪ α :=
  ⟨_, Quotient.out_injective⟩
#align function.embedding.quotient_out Function.Embedding.quotientOut
-/

#print Function.Embedding.coe_quotientOut /-
@[simp]
theorem coe_quotientOut (α) [s : Setoid α] : ⇑(quotientOut α) = Quotient.out :=
  rfl
#align function.embedding.coe_quotient_out Function.Embedding.coe_quotientOut
-/

#print Function.Embedding.punit /-
/-- Choosing an element `b : β` gives an embedding of `punit` into `β`. -/
def punit {β : Sort _} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by rintro ⟨⟩ ⟨⟩ _; rfl⟩
#align function.embedding.punit Function.Embedding.punit
-/

#print Function.Embedding.sectl /-
/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
@[simps]
def sectl (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun a a' h => congr_arg Prod.fst h⟩
#align function.embedding.sectl Function.Embedding.sectl
-/

#print Function.Embedding.sectr /-
/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
@[simps]
def sectr {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun b b' h => congr_arg Prod.snd h⟩
#align function.embedding.sectr Function.Embedding.sectr
-/

#print Function.Embedding.prodMap /-
/-- If `e₁` and `e₂` are embeddings, then so is `prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prodMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.Injective.Prod_map e₂.Injective⟩
#align function.embedding.prod_map Function.Embedding.prodMap
-/

#print Function.Embedding.coe_prodMap /-
@[simp]
theorem coe_prodMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
    ⇑(e₁.Prod_map e₂) = Prod.map e₁ e₂ :=
  rfl
#align function.embedding.coe_prod_map Function.Embedding.coe_prodMap
-/

#print Function.Embedding.pprodMap /-
/-- If `e₁` and `e₂` are embeddings, then so is `λ ⟨a, b⟩, ⟨e₁ a, e₂ b⟩ : pprod α γ → pprod β δ`. -/
def pprodMap {α β γ δ : Sort _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.Injective.pprod_map e₂.Injective⟩
#align function.embedding.pprod_map Function.Embedding.pprodMap
-/

section Sum

open Sum

#print Function.Embedding.sumMap /-
/-- If `e₁` and `e₂` are embeddings, then so is `sum.map e₁ e₂`. -/
def sumMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : Sum α γ ↪ Sum β δ :=
  ⟨Sum.map e₁ e₂, fun s₁ s₂ h =>
    match s₁, s₂, h with
    | inl a₁, inl a₂, h => congr_arg inl <| e₁.Injective <| inl.inj h
    | inr b₁, inr b₂, h => congr_arg inr <| e₂.Injective <| inr.inj h⟩
#align function.embedding.sum_map Function.Embedding.sumMap
-/

#print Function.Embedding.coe_sumMap /-
@[simp]
theorem coe_sumMap {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑(sumMap e₁ e₂) = Sum.map e₁ e₂ :=
  rfl
#align function.embedding.coe_sum_map Function.Embedding.coe_sumMap
-/

#print Function.Embedding.inl /-
/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
def inl {α β : Type _} : α ↪ Sum α β :=
  ⟨Sum.inl, fun a b => Sum.inl.inj⟩
#align function.embedding.inl Function.Embedding.inl
-/

#print Function.Embedding.inr /-
/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
def inr {α β : Type _} : β ↪ Sum α β :=
  ⟨Sum.inr, fun a b => Sum.inr.inj⟩
#align function.embedding.inr Function.Embedding.inr
-/

end Sum

section Sigma

variable {α α' : Type _} {β : α → Type _} {β' : α' → Type _}

#print Function.Embedding.sigmaMk /-
/-- `sigma.mk` as an `function.embedding`. -/
@[simps apply]
def sigmaMk (a : α) : β a ↪ Σ x, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩
#align function.embedding.sigma_mk Function.Embedding.sigmaMk
-/

#print Function.Embedding.sigmaMap /-
/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `sigma.map f g` is an embedding. -/
@[simps apply]
def sigmaMap (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σ a, β a) ↪ Σ a', β' a' :=
  ⟨Sigma.map f fun a => g a, f.Injective.sigma_map fun a => (g a).Injective⟩
#align function.embedding.sigma_map Function.Embedding.sigmaMap
-/

end Sigma

#print Function.Embedding.piCongrRight /-
/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `λ a, e a (f a)`. -/
@[simps]
def piCongrRight {α : Sort _} {β γ : α → Sort _} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun f₁ f₂ h => funext fun a => (e a).Injective (congr_fun h a)⟩
#align function.embedding.Pi_congr_right Function.Embedding.piCongrRight
-/

#print Function.Embedding.arrowCongrRight /-
/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  piCongrRight fun _ => e
#align function.embedding.arrow_congr_right Function.Embedding.arrowCongrRight
-/

#print Function.Embedding.arrowCongrRight_apply /-
@[simp]
theorem arrowCongrRight_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ ↪ α) :
    arrowCongrRight e f = e ∘ f :=
  rfl
#align function.embedding.arrow_congr_right_apply Function.Embedding.arrowCongrRight_apply
-/

#print Function.Embedding.arrowCongrLeft /-
/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
noncomputable def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) :
    (α → γ) ↪ β → γ :=
  ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩
#align function.embedding.arrow_congr_left Function.Embedding.arrowCongrLeft
-/

#print Function.Embedding.subtypeMap /-
/-- Restrict both domain and codomain of an embedding. -/
protected def subtypeMap {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
    (h : ∀ ⦃x⦄, p x → q (f x)) : { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩
#align function.embedding.subtype_map Function.Embedding.subtypeMap
-/

open Set

#print Function.Embedding.swap_apply /-
theorem swap_apply {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  f.Injective.swap_apply x y z
#align function.embedding.swap_apply Function.Embedding.swap_apply
-/

#print Function.Embedding.swap_comp /-
theorem swap_comp {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  f.Injective.swap_comp x y
#align function.embedding.swap_comp Function.Embedding.swap_comp
-/

end Embedding

end Function

namespace Equiv

open Function.Embedding

#print Equiv.subtypeInjectiveEquivEmbedding /-
/-- The type of embeddings `α ↪ β` is equivalent to
    the subtype of all injective functions `α → β`. -/
def subtypeInjectiveEquivEmbedding (α β : Sort _) : { f : α → β // Function.Injective f } ≃ (α ↪ β)
    where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.Injective⟩
  left_inv f := by simp
  right_inv f := by ext; rfl
#align equiv.subtype_injective_equiv_embedding Equiv.subtypeInjectiveEquivEmbedding
-/

#print Equiv.embeddingCongr /-
/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[congr, simps apply]
def embeddingCongr {α β γ δ : Sort _} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ)
    where
  toFun f := f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
#align equiv.embedding_congr Equiv.embeddingCongr
-/

#print Equiv.embeddingCongr_refl /-
@[simp]
theorem embeddingCongr_refl {α β : Sort _} :
    embeddingCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ↪ β) := by ext; rfl
#align equiv.embedding_congr_refl Equiv.embeddingCongr_refl
-/

#print Equiv.embeddingCongr_trans /-
@[simp]
theorem embeddingCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
    (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    embeddingCongr (e₁.trans e₂) (e₁'.trans e₂') =
      (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂') :=
  rfl
#align equiv.embedding_congr_trans Equiv.embeddingCongr_trans
-/

#print Equiv.embeddingCongr_symm /-
@[simp]
theorem embeddingCongr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm :=
  rfl
#align equiv.embedding_congr_symm Equiv.embeddingCongr_symm
-/

#print Equiv.embeddingCongr_apply_trans /-
theorem embeddingCongr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
    (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equiv.embeddingCongr ea ec (f.trans g) =
      (Equiv.embeddingCongr ea eb f).trans (Equiv.embeddingCongr eb ec g) :=
  by ext; simp
#align equiv.embedding_congr_apply_trans Equiv.embeddingCongr_apply_trans
-/

#print Equiv.refl_toEmbedding /-
@[simp]
theorem refl_toEmbedding {α : Type _} : (Equiv.refl α).toEmbedding = Function.Embedding.refl α :=
  rfl
#align equiv.refl_to_embedding Equiv.refl_toEmbedding
-/

#print Equiv.trans_toEmbedding /-
@[simp]
theorem trans_toEmbedding {α β γ : Type _} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding :=
  rfl
#align equiv.trans_to_embedding Equiv.trans_toEmbedding
-/

end Equiv

section Subtype

variable {α : Type _}

#print subtypeOrLeftEmbedding /-
/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] :
    { x // p x ∨ q x } ↪ Sum { x // p x } { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.Prop.resolve_left h⟩,
    by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩
#align subtype_or_left_embedding subtypeOrLeftEmbedding
-/

#print subtypeOrLeftEmbedding_apply_left /-
theorem subtypeOrLeftEmbedding_apply_left {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : p x) : subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dif_pos hx
#align subtype_or_left_embedding_apply_left subtypeOrLeftEmbedding_apply_left
-/

#print subtypeOrLeftEmbedding_apply_right /-
theorem subtypeOrLeftEmbedding_apply_right {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.Prop.resolve_left hx⟩ :=
  dif_neg hx
#align subtype_or_left_embedding_apply_right subtypeOrLeftEmbedding_apply_right
-/

#print Subtype.impEmbedding /-
/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps]
def Subtype.impEmbedding (p q : α → Prop) (h : ∀ x, p x → q x) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.Prop⟩, fun x y => by simp [Subtype.ext_iff]⟩
#align subtype.imp_embedding Subtype.impEmbedding
-/

end Subtype

