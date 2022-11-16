/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Data.Nat.Cast.Prod
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Logic.Function.Iterate

/-!
# The group of permutations (self-equivalences) of a type `α`

This file defines the `group` structure on `equiv.perm α`.
-/


universe u v

namespace Equiv

variable {α : Type u} {β : Type v}

namespace Perm

instance permGroup : Group (Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_left_inv := self_trans_symm
#align equiv.perm.perm_group Equiv.Perm.permGroup

/-- The permutation of a type is equivalent to the units group of the endomorphisms monoid of this
type. -/
@[simps]
def equivUnitsEnd : Perm α ≃* Units (Function.EndCat α) where
  toFun e := ⟨e, e.symm, e.self_comp_symm, e.symm_comp_self⟩
  invFun u := ⟨(u : Function.EndCat α), (↑u⁻¹ : Function.EndCat α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  left_inv e := ext fun x => rfl
  right_inv u := Units.ext rfl
  map_mul' e₁ e₂ := rfl
#align equiv.perm.equiv_units_End Equiv.Perm.equivUnitsEnd

/-- Lift a monoid homomorphism `f : G →* function.End α` to a monoid homomorphism
`f : G →* equiv.perm α`. -/
@[simps]
def _root_.monoid_hom.to_hom_perm {G : Type _} [Group G] (f : G →* Function.EndCat α) : G →* Perm α :=
  equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits
#align equiv.perm._root_.monoid_hom.to_hom_perm equiv.perm._root_.monoid_hom.to_hom_perm

theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
  Equiv.trans_apply _ _ _
#align equiv.perm.mul_apply Equiv.Perm.mul_apply

theorem one_apply (x) : (1 : Perm α) x = x :=
  rfl
#align equiv.perm.one_apply Equiv.Perm.one_apply

@[simp]
theorem inv_apply_self (f : Perm α) (x) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x
#align equiv.perm.inv_apply_self Equiv.Perm.inv_apply_self

@[simp]
theorem apply_inv_self (f : Perm α) (x) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x
#align equiv.perm.apply_inv_self Equiv.Perm.apply_inv_self

theorem one_def : (1 : Perm α) = Equiv.refl α :=
  rfl
#align equiv.perm.one_def Equiv.Perm.one_def

theorem mul_def (f g : Perm α) : f * g = g.trans f :=
  rfl
#align equiv.perm.mul_def Equiv.Perm.mul_def

theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
  rfl
#align equiv.perm.inv_def Equiv.Perm.inv_def

@[simp]
protected theorem coe_mul (f g : Perm α) : ⇑(f * g) = f ∘ g :=
  rfl
#align equiv.perm.coe_mul Equiv.Perm.coe_mul

@[simp]
protected theorem coe_one : ⇑(1 : Perm α) = id :=
  rfl
#align equiv.perm.coe_one Equiv.Perm.coe_one

theorem eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  f.eq_symm_apply
#align equiv.perm.eq_inv_iff_eq Equiv.Perm.eq_inv_iff_eq

theorem inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  f.symm_apply_eq
#align equiv.perm.inv_eq_iff_eq Equiv.Perm.inv_eq_iff_eq

theorem zpow_apply_comm {α : Type _} (σ : Perm α) (m n : ℤ) {x : α} : (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, zpow_mul_comm]
#align equiv.perm.zpow_apply_comm Equiv.Perm.zpow_apply_comm

@[simp]
theorem iterate_eq_pow (f : Perm α) : ∀ n, f^[n] = ⇑(f ^ n)
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ, pow_add, iterate_eq_pow]
    rfl
#align equiv.perm.iterate_eq_pow Equiv.Perm.iterate_eq_pow

/-! Lemmas about mixing `perm` with `equiv`. Because we have multiple ways to express
`equiv.refl`, `equiv.symm`, and `equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/


@[simp]
theorem trans_one {α : Sort _} {β : Type _} (e : α ≃ β) : e.trans (1 : Perm β) = e :=
  Equiv.trans_refl e
#align equiv.perm.trans_one Equiv.Perm.trans_one

@[simp]
theorem mul_refl (e : Perm α) : e * Equiv.refl α = e :=
  Equiv.trans_refl e
#align equiv.perm.mul_refl Equiv.Perm.mul_refl

@[simp]
theorem one_symm : (1 : Perm α).symm = 1 :=
  Equiv.refl_symm
#align equiv.perm.one_symm Equiv.Perm.one_symm

@[simp]
theorem refl_inv : (Equiv.refl α : Perm α)⁻¹ = 1 :=
  Equiv.refl_symm
#align equiv.perm.refl_inv Equiv.Perm.refl_inv

@[simp]
theorem one_trans {α : Type _} {β : Sort _} (e : α ≃ β) : (1 : Perm α).trans e = e :=
  Equiv.refl_trans e
#align equiv.perm.one_trans Equiv.Perm.one_trans

@[simp]
theorem refl_mul (e : Perm α) : Equiv.refl α * e = e :=
  Equiv.refl_trans e
#align equiv.perm.refl_mul Equiv.Perm.refl_mul

@[simp]
theorem inv_trans_self (e : Perm α) : e⁻¹.trans e = 1 :=
  Equiv.symm_trans_self e
#align equiv.perm.inv_trans_self Equiv.Perm.inv_trans_self

@[simp]
theorem mul_symm (e : Perm α) : e * e.symm = 1 :=
  Equiv.symm_trans_self e
#align equiv.perm.mul_symm Equiv.Perm.mul_symm

@[simp]
theorem self_trans_inv (e : Perm α) : e.trans e⁻¹ = 1 :=
  Equiv.self_trans_symm e
#align equiv.perm.self_trans_inv Equiv.Perm.self_trans_inv

@[simp]
theorem symm_mul (e : Perm α) : e.symm * e = 1 :=
  Equiv.self_trans_symm e
#align equiv.perm.symm_mul Equiv.Perm.symm_mul

/-! Lemmas about `equiv.perm.sum_congr` re-expressed via the group structure. -/


@[simp]
theorem sum_congr_mul {α β : Type _} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β) :
    sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h) :=
  sum_congr_trans g h e f
#align equiv.perm.sum_congr_mul Equiv.Perm.sum_congr_mul

@[simp]
theorem sum_congr_inv {α β : Type _} (e : Perm α) (f : Perm β) : (sumCongr e f)⁻¹ = sumCongr e⁻¹ f⁻¹ :=
  sum_congr_symm e f
#align equiv.perm.sum_congr_inv Equiv.Perm.sum_congr_inv

@[simp]
theorem sum_congr_one {α β : Type _} : sumCongr (1 : Perm α) (1 : Perm β) = 1 :=
  sum_congr_refl
#align equiv.perm.sum_congr_one Equiv.Perm.sum_congr_one

/-- `equiv.perm.sum_congr` as a `monoid_hom`, with its two arguments bundled into a single `prod`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
def sumCongrHom (α β : Type _) : Perm α × Perm β →* Perm (Sum α β) where
  toFun a := sumCongr a.1 a.2
  map_one' := sum_congr_one
  map_mul' a b := (sum_congr_mul _ _ _ _).symm
#align equiv.perm.sum_congr_hom Equiv.Perm.sumCongrHom

theorem sum_congr_hom_injective {α β : Type _} : Function.Injective (sumCongrHom α β) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iff]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
    
  · simpa using Equiv.congr_fun h (Sum.inr i)
    
#align equiv.perm.sum_congr_hom_injective Equiv.Perm.sum_congr_hom_injective

@[simp]
theorem sum_congr_swap_one {α β : Type _} [DecidableEq α] [DecidableEq β] (i j : α) :
    sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  sum_congr_swap_refl i j
#align equiv.perm.sum_congr_swap_one Equiv.Perm.sum_congr_swap_one

@[simp]
theorem sum_congr_one_swap {α β : Type _} [DecidableEq α] [DecidableEq β] (i j : β) :
    sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  sum_congr_refl_swap i j
#align equiv.perm.sum_congr_one_swap Equiv.Perm.sum_congr_one_swap

/-! Lemmas about `equiv.perm.sigma_congr_right` re-expressed via the group structure. -/


@[simp]
theorem sigma_congr_right_mul {α : Type _} {β : α → Type _} (F : ∀ a, Perm (β a)) (G : ∀ a, Perm (β a)) :
    sigmaCongrRight F * sigmaCongrRight G = sigmaCongrRight (F * G) :=
  sigma_congr_right_trans G F
#align equiv.perm.sigma_congr_right_mul Equiv.Perm.sigma_congr_right_mul

@[simp]
theorem sigma_congr_right_inv {α : Type _} {β : α → Type _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹ :=
  sigma_congr_right_symm F
#align equiv.perm.sigma_congr_right_inv Equiv.Perm.sigma_congr_right_inv

@[simp]
theorem sigma_congr_right_one {α : Type _} {β : α → Type _} : sigmaCongrRight (1 : ∀ a, Equiv.Perm <| β a) = 1 :=
  sigma_congr_right_refl
#align equiv.perm.sigma_congr_right_one Equiv.Perm.sigma_congr_right_one

/-- `equiv.perm.sigma_congr_right` as a `monoid_hom`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
def sigmaCongrRightHom {α : Type _} (β : α → Type _) : (∀ a, Perm (β a)) →* Perm (Σa, β a) where
  toFun := sigmaCongrRight
  map_one' := sigma_congr_right_one
  map_mul' a b := (sigma_congr_right_mul _ _).symm
#align equiv.perm.sigma_congr_right_hom Equiv.Perm.sigmaCongrRightHom

theorem sigma_congr_right_hom_injective {α : Type _} {β : α → Type _} : Function.Injective (sigmaCongrRightHom β) := by
  intro x y h
  ext (a b)
  simpa using Equiv.congr_fun h ⟨a, b⟩
#align equiv.perm.sigma_congr_right_hom_injective Equiv.Perm.sigma_congr_right_hom_injective

/-- `equiv.perm.subtype_congr` as a `monoid_hom`. -/
@[simps]
def subtypeCongrHom (p : α → Prop) [DecidablePred p] : Perm { a // p a } × Perm { a // ¬p a } →* Perm α where
  toFun pair := Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm
#align equiv.perm.subtype_congr_hom Equiv.Perm.subtypeCongrHom

theorem subtype_congr_hom_injective (p : α → Prop) [DecidablePred p] : Function.Injective (subtypeCongrHom p) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iff]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i
#align equiv.perm.subtype_congr_hom_injective Equiv.Perm.subtype_congr_hom_injective

/-- If `e` is also a permutation, we can write `perm_congr`
completely in terms of the group structure. -/
@[simp]
theorem perm_congr_eq_mul (e p : Perm α) : e.permCongr p = e * p * e⁻¹ :=
  rfl
#align equiv.perm.perm_congr_eq_mul Equiv.Perm.perm_congr_eq_mul

section ExtendDomain

/-! Lemmas about `equiv.perm.extend_domain` re-expressed via the group structure. -/


variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

@[simp]
theorem extend_domain_one : extendDomain 1 f = 1 :=
  extend_domain_refl f
#align equiv.perm.extend_domain_one Equiv.Perm.extend_domain_one

@[simp]
theorem extend_domain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f :=
  rfl
#align equiv.perm.extend_domain_inv Equiv.Perm.extend_domain_inv

@[simp]
theorem extend_domain_mul (e e' : Perm α) : e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f :=
  extend_domain_trans _ _ _
#align equiv.perm.extend_domain_mul Equiv.Perm.extend_domain_mul

/-- `extend_domain` as a group homomorphism -/
@[simps]
def extendDomainHom : Perm α →* Perm β where
  toFun e := extendDomain e f
  map_one' := extend_domain_one f
  map_mul' e e' := (extend_domain_mul f e e').symm
#align equiv.perm.extend_domain_hom Equiv.Perm.extendDomainHom

theorem extend_domain_hom_injective : Function.Injective (extendDomainHom f) :=
  (injective_iff_map_eq_one (extendDomainHom f)).mpr fun e he =>
    ext fun x => f.Injective (Subtype.ext ((extend_domain_apply_image e f x).symm.trans (ext_iff.mp he (f x))))
#align equiv.perm.extend_domain_hom_injective Equiv.Perm.extend_domain_hom_injective

@[simp]
theorem extend_domain_eq_one_iff {e : Perm α} {f : α ≃ Subtype p} : e.extendDomain f = 1 ↔ e = 1 :=
  (injective_iff_map_eq_one' (extendDomainHom f)).mp (extend_domain_hom_injective f) e
#align equiv.perm.extend_domain_eq_one_iff Equiv.Perm.extend_domain_eq_one_iff

end ExtendDomain

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtypePerm (f : Perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) : Perm { x // p x } :=
  ⟨fun x => ⟨f x, (h _).1 x.2⟩, fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).2 <| by simpa using x.2⟩, fun _ => by
    simp only [perm.inv_apply_self, Subtype.coe_eta, Subtype.coe_mk], fun _ => by
    simp only [perm.apply_inv_self, Subtype.coe_eta, Subtype.coe_mk]⟩
#align equiv.perm.subtype_perm Equiv.Perm.subtypePerm

@[simp]
theorem subtype_perm_apply (f : Perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) (x : { x // p x }) :
    subtypePerm f h x = ⟨f x, (h _).1 x.2⟩ :=
  rfl
#align equiv.perm.subtype_perm_apply Equiv.Perm.subtype_perm_apply

@[simp]
theorem subtype_perm_one (p : α → Prop) (h : ∀ x, p x ↔ p ((1 : Perm α) x)) : @subtypePerm α 1 p h = 1 :=
  Equiv.ext fun ⟨_, _⟩ => rfl
#align equiv.perm.subtype_perm_one Equiv.Perm.subtype_perm_one

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def ofSubtype {p : α → Prop} [DecidablePred p] : Perm (Subtype p) →* Perm α where
  toFun f := extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extend_domain_one _
  map_mul' f g := (Equiv.Perm.extend_domain_mul _ f g).symm
#align equiv.perm.of_subtype Equiv.Perm.ofSubtype

theorem of_subtype_subtype_perm {f : Perm α} {p : α → Prop} [DecidablePred p] (h₁ : ∀ x, p x ↔ p (f x))
    (h₂ : ∀ x, f x ≠ x → p x) : ofSubtype (subtypePerm f h₁) = f :=
  Equiv.ext fun x => by
    by_cases hx:p x
    · exact (subtype_perm f h₁).extend_domain_apply_subtype _ hx
      
    · rw [of_subtype, MonoidHom.coe_mk, Equiv.Perm.extend_domain_apply_not_subtype]
      · exact not_not.mp fun h => hx (h₂ x (Ne.symm h))
        
      · exact hx
        
      
#align equiv.perm.of_subtype_subtype_perm Equiv.Perm.of_subtype_subtype_perm

theorem of_subtype_apply_of_mem {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p)) {x : α} (hx : p x) :
    ofSubtype f x = f ⟨x, hx⟩ :=
  extend_domain_apply_subtype f _ hx
#align equiv.perm.of_subtype_apply_of_mem Equiv.Perm.of_subtype_apply_of_mem

@[simp]
theorem of_subtype_apply_coe {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p)) (x : Subtype p) :
    ofSubtype f x = f x :=
  (Subtype.casesOn x) fun _ => of_subtype_apply_of_mem f
#align equiv.perm.of_subtype_apply_coe Equiv.Perm.of_subtype_apply_coe

theorem of_subtype_apply_of_not_mem {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p)) {x : α} (hx : ¬p x) :
    ofSubtype f x = x :=
  extend_domain_apply_not_subtype f (Equiv.refl (Subtype p)) hx
#align equiv.perm.of_subtype_apply_of_not_mem Equiv.Perm.of_subtype_apply_of_not_mem

theorem mem_iff_of_subtype_apply_mem {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p)) (x : α) :
    p x ↔ p ((ofSubtype f : α → α) x) :=
  if h : p x then by simpa only [h, true_iff_iff, MonoidHom.coe_mk, of_subtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, of_subtype_apply_of_not_mem f h]
#align equiv.perm.mem_iff_of_subtype_apply_mem Equiv.Perm.mem_iff_of_subtype_apply_mem

@[simp]
theorem subtype_perm_of_subtype {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p)) :
    subtypePerm (ofSubtype f) (mem_iff_of_subtype_apply_mem f) = f :=
  Equiv.ext fun ⟨x, hx⟩ => Subtype.coe_injective (of_subtype_apply_of_mem f hx)
#align equiv.perm.subtype_perm_of_subtype Equiv.Perm.subtype_perm_of_subtype

@[simp]
theorem default_perm {n : Type _} : (default : Perm n) = 1 :=
  rfl
#align equiv.perm.default_perm Equiv.Perm.default_perm

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps]
protected def subtypeEquivSubtypePerm (p : α → Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a → f a = a } where
  toFun f := ⟨f.ofSubtype, fun a => f.of_subtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun a =>
      ⟨Decidable.not_imp_not.1 fun hfa => f.val.Injective (f.Prop _ hfa) ▸ hfa,
        Decidable.not_imp_not.1 fun ha hfa => ha <| f.Prop a ha ▸ hfa⟩
  left_inv := Equiv.Perm.subtype_perm_of_subtype
  right_inv f := Subtype.ext ((Equiv.Perm.of_subtype_subtype_perm _) fun a => Not.decidable_imp_symm <| f.Prop a)
#align equiv.perm.subtype_equiv_subtype_perm Equiv.Perm.subtypeEquivSubtypePerm

theorem subtype_equiv_subtype_perm_apply_of_mem {α : Type _} {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p))
    {a : α} (h : p a) : Perm.subtypeEquivSubtypePerm p f a = f ⟨a, h⟩ :=
  f.of_subtype_apply_of_mem h
#align equiv.perm.subtype_equiv_subtype_perm_apply_of_mem Equiv.Perm.subtype_equiv_subtype_perm_apply_of_mem

theorem subtype_equiv_subtype_perm_apply_of_not_mem {α : Type _} {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p))
    {a : α} (h : ¬p a) : Perm.subtypeEquivSubtypePerm p f a = a :=
  f.of_subtype_apply_of_not_mem h
#align equiv.perm.subtype_equiv_subtype_perm_apply_of_not_mem Equiv.Perm.subtype_equiv_subtype_perm_apply_of_not_mem

end Perm

section Swap

variable [DecidableEq α]

@[simp]
theorem swap_inv (x y : α) : (swap x y)⁻¹ = swap x y :=
  rfl
#align equiv.swap_inv Equiv.swap_inv

@[simp]
theorem swap_mul_self (i j : α) : swap i j * swap i j = 1 :=
  swap_swap i j
#align equiv.swap_mul_self Equiv.swap_mul_self

theorem swap_mul_eq_mul_swap (f : Perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
  Equiv.ext fun z => by
    simp only [perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all only [perm.apply_inv_self, perm.eq_inv_iff_eq, eq_self_iff_true, not_true]
#align equiv.swap_mul_eq_mul_swap Equiv.swap_mul_eq_mul_swap

theorem mul_swap_eq_swap_mul (f : Perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f := by
  rw [swap_mul_eq_mul_swap, perm.inv_apply_self, perm.inv_apply_self]
#align equiv.mul_swap_eq_swap_mul Equiv.mul_swap_eq_swap_mul

theorem swap_apply_apply (f : Perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ := by
  rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]
#align equiv.swap_apply_apply Equiv.swap_apply_apply

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem swap_mul_self_mul (i j : α) (σ : Perm α) : Equiv.swap i j * (Equiv.swap i j * σ) = σ := by
  rw [← mul_assoc, swap_mul_self, one_mul]
#align equiv.swap_mul_self_mul Equiv.swap_mul_self_mul

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem mul_swap_mul_self (i j : α) (σ : Perm α) : σ * Equiv.swap i j * Equiv.swap i j = σ := by
  rw [mul_assoc, swap_mul_self, mul_one]
#align equiv.mul_swap_mul_self Equiv.mul_swap_mul_self

/-- A stronger version of `mul_right_injective` -/
@[simp]
theorem swap_mul_involutive (i j : α) : Function.Involutive ((· * ·) (Equiv.swap i j)) :=
  swap_mul_self_mul i j
#align equiv.swap_mul_involutive Equiv.swap_mul_involutive

/-- A stronger version of `mul_left_injective` -/
@[simp]
theorem mul_swap_involutive (i j : α) : Function.Involutive (· * Equiv.swap i j) :=
  mul_swap_mul_self i j
#align equiv.mul_swap_involutive Equiv.mul_swap_involutive

@[simp]
theorem swap_eq_one_iff {i j : α} : swap i j = (1 : Perm α) ↔ i = j :=
  swap_eq_refl_iff
#align equiv.swap_eq_one_iff Equiv.swap_eq_one_iff

theorem swap_mul_eq_iff {i j : α} {σ : Perm α} : swap i j * σ = σ ↔ i = j :=
  ⟨fun h => by
    have swap_id : swap i j = 1 := mul_right_cancel (trans h (one_mul σ).symm)
    rw [← swap_apply_right i j, swap_id]
    rfl, fun h => by erw [h, swap_self, one_mul]⟩
#align equiv.swap_mul_eq_iff Equiv.swap_mul_eq_iff

theorem mul_swap_eq_iff {i j : α} {σ : Perm α} : σ * swap i j = σ ↔ i = j :=
  ⟨fun h => by
    have swap_id : swap i j = 1 := mul_left_cancel (trans h (one_mul σ).symm)
    rw [← swap_apply_right i j, swap_id]
    rfl, fun h => by erw [h, swap_self, mul_one]⟩
#align equiv.mul_swap_eq_iff Equiv.mul_swap_eq_iff

theorem swap_mul_swap_mul_swap {x y z : α} (hwz : x ≠ y) (hxz : x ≠ z) : swap y z * swap x y * swap y z = swap z x :=
  Equiv.ext fun n => by
    simp only [swap_apply_def, perm.mul_apply]
    split_ifs <;> cc
#align equiv.swap_mul_swap_mul_swap Equiv.swap_mul_swap_mul_swap

end Swap

end Equiv

