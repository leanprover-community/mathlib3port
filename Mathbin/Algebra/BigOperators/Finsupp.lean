/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Data.Finsupp.Defs
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.BigOperators.Order

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/


noncomputable section

open Finset Function

open Classical BigOperators

variable {α ι γ A B C : Type _} [AddCommMonoidₓ A] [AddCommMonoidₓ B] [AddCommMonoidₓ C]

variable {t : ι → A → C} (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y)

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type _}

namespace Finsupp

/-!
### Declarations about `sum` and `prod`

In most of this section, the domain `β` is assumed to be an `add_monoid`.
-/


section SumProd

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g a (f a)` over the support of `f`. "]
def prod [Zero M] [CommMonoidₓ N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏ a in f.Support, g a (f a)

variable [Zero M] [Zero M'] [CommMonoidₓ N]

@[to_additive]
theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.Support ⊆ s) (g : α → M → N)
    (h : ∀ i ∈ s, g i 0 = 1) : f.Prod g = ∏ x in s, g x (f x) :=
  (Finset.prod_subset hs) fun x hxs hx => h x hxs ▸ congr_arg (g x) <| not_mem_support_iff.1 hx

@[to_additive]
theorem prod_fintype [Fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) : f.Prod g = ∏ i, g i (f i) :=
  f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[simp, to_additive]
theorem prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) : (single a b).Prod h = h a b :=
  calc
    (single a b).Prod h = ∏ x in {a}, h x (single a b x) :=
      (prod_of_support_subset _ support_single_subset h) fun x hx => (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by
      simp
    

@[to_additive]
theorem prod_map_range_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N} (h0 : ∀ a, h a 0 = 1) :
    (mapRange f hf g).Prod h = g.Prod fun a b => h a (f b) :=
  (Finset.prod_subset support_map_range) fun _ _ H => by
    rw [not_mem_support_iff.1 H, h0]

@[simp, to_additive]
theorem prod_zero_index {h : α → M → N} : (0 : α →₀ M).Prod h = 1 :=
  rfl

@[to_additive]
theorem prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
    (f.Prod fun x v => g.Prod fun x' v' => h x v x' v') = g.Prod fun x' v' => f.Prod fun x v => h x v x' v' :=
  Finset.prod_comm

@[simp, to_additive]
theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.Prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.Support) (b a (f a)) 1 := by
  dsimp' [Finsupp.prod]
  rw [f.support.prod_ite_eq]

@[simp]
theorem sum_ite_self_eq [DecidableEq α] {N : Type _} [AddCommMonoidₓ N] (f : α →₀ N) (a : α) :
    (f.Sum fun x v => ite (a = x) v 0) = f a := by
  convert f.sum_ite_eq a fun x => id
  simp [ite_eq_right_iff.2 Eq.symm]

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[simp, to_additive "A restatement of `sum_ite_eq` with the equality test reversed."]
theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.Prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.Support) (b a (f a)) 1 := by
  dsimp' [Finsupp.prod]
  rw [f.support.prod_ite_eq']

@[simp]
theorem sum_ite_self_eq' [DecidableEq α] {N : Type _} [AddCommMonoidₓ N] (f : α →₀ N) (a : α) :
    (f.Sum fun x v => ite (x = a) v 0) = f a := by
  convert f.sum_ite_eq' a fun x => id
  simp [ite_eq_right_iff.2 Eq.symm]

@[simp]
theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) : (f.Prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  (f.prod_fintype _) fun a => pow_zeroₓ _

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `on_finset` is the same as multiplying it over the original
`finset`. -/
@[to_additive
      "If `g` maps a second argument of 0 to 0, summing it over the\nresult of `on_finset` is the same as summing it over the original\n`finset`."]
theorem on_finset_prod {s : Finset α} {f : α → M} {g : α → M → N} (hf : ∀ a, f a ≠ 0 → a ∈ s) (hg : ∀ a, g a 0 = 1) :
    (onFinset s f hf).Prod g = ∏ a in s, g a (f a) :=
  Finset.prod_subset support_on_finset_subset <| by
    simp (config := { contextual := true })[*]

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive
      " Taking a sum over over `f : α →₀ M` is the same as adding the value on a\nsingle element `y ∈ f.support` to the sum over `erase y f`. "]
theorem mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.Support) :
    g y (f y) * (erase y f).Prod g = f.Prod g := by
  rw [Finsupp.prod, Finsupp.prod, ← Finset.mul_prod_erase _ _ hyf, Finsupp.support_erase, Finset.prod_congr rfl]
  intro h hx
  rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

/-- Generalization of `finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive
      " Generalization of `finsupp.add_sum_erase`: if `g` maps a second argument of 0\nto 0, then its sum over `f : α →₀ M` is the same as adding the value on any element\n`y : α` to the sum over `erase y f`. "]
theorem mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ i : α, g i 0 = 1) :
    g y (f y) * (erase y f).Prod g = f.Prod g := by
  classical
  by_cases' hyf : y ∈ f.support
  · exact Finsupp.mul_prod_erase f y g hyf
    
  · rw [not_mem_support_iff.mp hyf, hg y, erase_of_not_mem_support hyf, one_mulₓ]
    

@[to_additive]
theorem _root_.submonoid_class.finsupp_prod_mem {S : Type _} [SetLike S N] [SubmonoidClass S N] (s : S) (f : α →₀ M)
    (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.Prod g ∈ s :=
  prod_mem fun i hi => h _ (Finsupp.mem_support_iff.mp hi)

@[to_additive]
theorem prod_congr {f : α →₀ M} {g1 g2 : α → M → N} (h : ∀ x ∈ f.Support, g1 x (f x) = g2 x (f x)) :
    f.Prod g1 = f.Prod g2 :=
  Finset.prod_congr rfl h

end SumProd

end Finsupp

@[to_additive]
theorem map_finsupp_prod [Zero M] [CommMonoidₓ N] [CommMonoidₓ P] {H : Type _} [MonoidHomClass H N P] (h : H)
    (f : α →₀ M) (g : α → M → N) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_prod h _ _

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_finsupp_sum` instead."]
protected theorem MulEquiv.map_finsupp_prod [Zero M] [CommMonoidₓ N] [CommMonoidₓ P] (h : N ≃* P) (f : α →₀ M)
    (g : α → M → N) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_finsupp_prod h f g

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_finsupp_sum` instead."]
protected theorem MonoidHom.map_finsupp_prod [Zero M] [CommMonoidₓ N] [CommMonoidₓ P] (h : N →* P) (f : α →₀ M)
    (g : α → M → N) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_finsupp_prod h f g

/-- Deprecated, use `_root_.map_finsupp_sum` instead. -/
protected theorem RingHom.map_finsupp_sum [Zero M] [Semiringₓ R] [Semiringₓ S] (h : R →+* S) (f : α →₀ M)
    (g : α → M → R) : h (f.Sum g) = f.Sum fun a b => h (g a b) :=
  map_finsupp_sum h f g

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
protected theorem RingHom.map_finsupp_prod [Zero M] [CommSemiringₓ R] [CommSemiringₓ S] (h : R →+* S) (f : α →₀ M)
    (g : α → M → R) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_finsupp_prod h f g

@[to_additive]
theorem MonoidHom.coe_finsupp_prod [Zero β] [Monoidₓ N] [CommMonoidₓ P] (f : α →₀ β) (g : α → β → N →* P) :
    ⇑(f.Prod g) = f.Prod fun i fi => g i fi :=
  MonoidHom.coe_finset_prod _ _

@[simp, to_additive]
theorem MonoidHom.finsupp_prod_apply [Zero β] [Monoidₓ N] [CommMonoidₓ P] (f : α →₀ β) (g : α → β → N →* P) (x : N) :
    f.Prod g x = f.Prod fun i fi => g i fi x :=
  MonoidHom.finset_prod_apply _ _ _

namespace Finsupp

theorem single_multiset_sum [AddCommMonoidₓ M] (s : Multiset M) (a : α) : single a s.Sum = (s.map (single a)).Sum :=
  (Multiset.induction_on s (single_zero _)) fun a s ih => by
    rw [Multiset.sum_cons, single_add, ih, Multiset.map_cons, Multiset.sum_cons]

theorem single_finset_sum [AddCommMonoidₓ M] (s : Finset ι) (f : ι → M) (a : α) :
    single a (∑ b in s, f b) = ∑ b in s, single a (f b) := by
  trans
  apply single_multiset_sum
  rw [Multiset.map_map]
  rfl

theorem single_sum [Zero M] [AddCommMonoidₓ N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
    single a (s.Sum f) = s.Sum fun d c => single a (f d c) :=
  single_finset_sum _ _ _

@[to_additive]
theorem prod_neg_index [AddGroupₓ G] [CommMonoidₓ M] {g : α →₀ G} {h : α → G → M} (h0 : ∀ a, h a 0 = 1) :
    (-g).Prod h = g.Prod fun a b => h a (-b) :=
  prod_map_range_index h0

end Finsupp

namespace Finsupp

theorem finset_sum_apply [AddCommMonoidₓ N] (S : Finset ι) (f : ι → α →₀ N) (a : α) :
    (∑ i in S, f i) a = ∑ i in S, f i a :=
  (applyAddHom a : (α →₀ N) →+ _).map_sum _ _

@[simp]
theorem sum_apply [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
    (f.Sum g) a₂ = f.Sum fun a₁ b => g a₁ b a₂ :=
  finset_sum_apply _ _ _

theorem coe_finset_sum [AddCommMonoidₓ N] (S : Finset ι) (f : ι → α →₀ N) : ⇑(∑ i in S, f i) = ∑ i in S, f i :=
  (coeFnAddHom : (α →₀ N) →+ _).map_sum _ _

theorem coe_sum [Zero M] [AddCommMonoidₓ N] (f : α →₀ M) (g : α → M → β →₀ N) : ⇑(f.Sum g) = f.Sum fun a₁ b => g a₁ b :=
  coe_finset_sum _ _

theorem support_sum [DecidableEq β] [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} {g : α → M → β →₀ N} :
    (f.Sum g).Support ⊆ f.Support.bUnion fun a => (g a (f a)).Support := by
  have : ∀ c, (f.Sum fun a b => g a b c) ≠ 0 → ∃ a, f a ≠ 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, Ne⟩
  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_bUnion, sum_apply, exists_prop]

theorem support_finset_sum [DecidableEq β] [AddCommMonoidₓ M] {s : Finset α} {f : α → β →₀ M} :
    (Finset.sum s f).Support ⊆ s.bUnion fun x => (f x).Support := by
  rw [← Finset.sup_eq_bUnion]
  induction' s using Finset.cons_induction_on with a s ha ih
  · rfl
    
  · rw [Finset.sum_cons, Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)
    

@[simp]
theorem sum_zero [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} : (f.Sum fun a b => (0 : N)) = 0 :=
  Finset.sum_const_zero

@[simp, to_additive]
theorem prod_mul [Zero M] [CommMonoidₓ N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
    (f.Prod fun a b => h₁ a b * h₂ a b) = f.Prod h₁ * f.Prod h₂ :=
  Finset.prod_mul_distrib

@[simp, to_additive]
theorem prod_inv [Zero M] [CommGroupₓ G] {f : α →₀ M} {h : α → M → G} : (f.Prod fun a b => (h a b)⁻¹) = (f.Prod h)⁻¹ :=
  (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[simp]
theorem sum_sub [Zero M] [AddCommGroupₓ G] {f : α →₀ M} {h₁ h₂ : α → M → G} :
    (f.Sum fun a b => h₁ a b - h₂ a b) = f.Sum h₁ - f.Sum h₂ :=
  Finset.sum_sub_distrib

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism on the support.
This is a more general version of `finsupp.prod_add_index'`; the latter has simpler hypotheses. -/
@[to_additive
      "Taking the product under `h` is an additive homomorphism of finsupps,\nif `h` is an additive homomorphism on the support.\nThis is a more general version of `finsupp.sum_add_index'`; the latter has simpler hypotheses."]
theorem prod_add_index [AddZeroClassₓ M] [CommMonoidₓ N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀ a ∈ f.Support ∪ g.Support, h a 0 = 1)
    (h_add : ∀ a ∈ f.Support ∪ g.Support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).Prod h = f.Prod h * g.Prod h := by
  rw [Finsupp.prod_of_support_subset f (subset_union_left _ g.support) h h_zero,
    Finsupp.prod_of_support_subset g (subset_union_right f.support _) h h_zero, ← Finset.prod_mul_distrib,
    Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact
    Finset.prod_congr rfl fun x hx => by
      apply h_add x hx

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive
      "Taking the sum under `h` is an additive homomorphism of finsupps,\nif `h` is an additive homomorphism.\nThis is a more specific version of `finsupp.sum_add_index` with simpler hypotheses."]
theorem prod_add_index' [AddZeroClassₓ M] [CommMonoidₓ N] {f g : α →₀ M} {h : α → M → N} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) : (f + g).Prod h = f.Prod h * g.Prod h :=
  prod_add_index (fun a ha => h_zero a) fun a ha => h_add a

@[simp]
theorem sum_hom_add_index [AddZeroClassₓ M] [AddCommMonoidₓ N] {f g : α →₀ M} (h : α → M →+ N) :
    ((f + g).Sum fun x => h x) = (f.Sum fun x => h x) + g.Sum fun x => h x :=
  sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]
theorem prod_hom_add_index [AddZeroClassₓ M] [CommMonoidₓ N] {f g : α →₀ M} (h : α → Multiplicative M →* N) :
    ((f + g).Prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.Prod fun a b => h a (Multiplicative.ofAdd b)) * g.Prod fun a b => h a (Multiplicative.ofAdd b) :=
  prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def liftAddHom [AddZeroClassₓ M] [AddCommMonoidₓ N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) where
  toFun := fun F =>
    { toFun := fun f => f.Sum fun x => F x, map_zero' := Finset.sum_empty,
      map_add' := fun _ _ => sum_add_index' (fun x => (F x).map_zero) fun x => (F x).map_add }
  invFun := fun F x => F.comp <| singleAddHom x
  left_inv := fun F => by
    ext
    simp
  right_inv := fun F => by
    ext
    simp
  map_add' := fun F G => by
    ext
    simp

@[simp]
theorem lift_add_hom_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : α → M →+ N) (f : α →₀ M) :
    liftAddHom F f = f.Sum fun x => F x :=
  rfl

@[simp]
theorem lift_add_hom_symm_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : (α →₀ M) →+ N) (x : α) :
    liftAddHom.symm F x = F.comp (singleAddHom x) :=
  rfl

theorem lift_add_hom_symm_apply_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : (α →₀ M) →+ N) (x : α) (y : M) :
    liftAddHom.symm F x y = F (single x y) :=
  rfl

@[simp]
theorem lift_add_hom_single_add_hom [AddCommMonoidₓ M] :
    liftAddHom (singleAddHom : α → M →+ α →₀ M) = AddMonoidHom.id _ :=
  liftAddHom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

@[simp]
theorem sum_single [AddCommMonoidₓ M] (f : α →₀ M) : f.Sum single = f :=
  AddMonoidHom.congr_fun lift_add_hom_single_add_hom f

@[simp]
theorem sum_univ_single [AddCommMonoidₓ M] [Fintype α] (i : α) (m : M) : (∑ j : α, (single i m) j) = m := by
  simp [single]

@[simp]
theorem sum_univ_single' [AddCommMonoidₓ M] [Fintype α] (i : α) (m : M) : (∑ j : α, (single j m) i) = m := by
  simp [single]

@[simp]
theorem lift_add_hom_apply_single [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : α → M →+ N) (a : α) (b : M) :
    liftAddHom f (single a b) = f a b :=
  sum_single_index (f a).map_zero

@[simp]
theorem lift_add_hom_comp_single [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : α → M →+ N) (a : α) :
    (liftAddHom f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => lift_add_hom_apply_single f a b

theorem comp_lift_add_hom [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P] (g : N →+ P) (f : α → M →+ N) :
    g.comp (liftAddHom f) = liftAddHom fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [lift_add_hom_symm_apply, AddMonoidHom.comp_assoc, lift_add_hom_comp_single]

theorem sum_sub_index [AddCommGroupₓ β] [AddCommGroupₓ γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).Sum h = f.Sum h - g.Sum h :=
  (liftAddHom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[to_additive]
theorem prod_emb_domain [Zero M] [CommMonoidₓ N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
    (v.embDomain f).Prod g = v.Prod fun a b => g (f a) b := by
  rw [Prod, Prod, support_emb_domain, Finset.prod_map]
  simp_rw [emb_domain_apply]

@[to_additive]
theorem prod_finset_sum_index [AddCommMonoidₓ M] [CommMonoidₓ N] {s : Finset ι} {g : ι → α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i in s, (g i).Prod h) = (∑ i in s, g i).Prod h :=
  (Finset.induction_on s rfl) fun a s has ih => by
    rw [prod_insert has, ih, sum_insert has, prod_add_index' h_zero h_add]

@[to_additive]
theorem prod_sum_index [AddCommMonoidₓ M] [AddCommMonoidₓ N] [CommMonoidₓ P] {f : α →₀ M} {g : α → M → β →₀ N}
    {h : β → N → P} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.Sum g).Prod h = f.Prod fun a b => (g a b).Prod h :=
  (prod_finset_sum_index h_zero h_add).symm

theorem multiset_sum_sum_index [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : Multiset (α →₀ M)) (h : α → M → N)
    (h₀ : ∀ a, h a 0 = 0) (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    f.Sum.Sum h = (f.map fun g : α →₀ M => g.Sum h).Sum :=
  (Multiset.induction_on f rfl) fun a s ih => by
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_index' h₀ h₁, ih]

theorem support_sum_eq_bUnion {α : Type _} {ι : Type _} {M : Type _} [AddCommMonoidₓ M] {g : ι → α →₀ M} (s : Finset ι)
    (h : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (g i₁).Support (g i₂).Support) :
    (∑ i in s, g i).Support = s.bUnion fun i => (g i).Support := by
  apply Finset.induction_on s
  · simp
    
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, bUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq, hs]
    rw [hs]
    intro x hx
    simp only [mem_bUnion, exists_prop, inf_eq_inter, Ne.def, mem_inter] at hx
    obtain ⟨hxi, j, hj, hxj⟩ := hx
    have hn : i ≠ j := fun H => hi (H.symm ▸ hj)
    apply h _ _ hn
    simp [hxi, hxj]
    

theorem multiset_map_sum [Zero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
    Multiset.map m (f.Sum h) = f.Sum fun a b => (h a b).map m :=
  (Multiset.mapAddMonoidHom m).map_sum _ f.Support

theorem multiset_sum_sum [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.Sum h) = f.Sum fun a b => Multiset.sum (h a b) :=
  (Multiset.sumAddMonoidHom : Multiset N →+ N).map_sum _ f.Support

/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
@[to_additive
      "For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`\nover `f1` and `f2` equals the sum of `g` over `f1 + f2`"]
theorem prod_add_index_of_disjoint [AddCommMonoidₓ M] {f1 f2 : α →₀ M} (hd : Disjoint f1.Support f2.Support)
    {β : Type _} [CommMonoidₓ β] (g : α → M → β) : (f1 + f2).Prod g = f1.Prod g * f2.Prod g := by
  have : ∀ {f1 f2 : α →₀ M}, Disjoint f1.Support f2.Support → (∏ x in f1.Support, g x (f1 x + f2 x)) = f1.Prod g :=
    fun f1 f2 hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [not_mem_support_iff.mp (disjoint_left.mp hd hx), add_zeroₓ]
  simp_rw [← this hd, ← this hd.symm, add_commₓ (f2 _), Finsupp.prod, support_add_eq hd, prod_union hd, add_apply]

theorem prod_dvd_prod_of_subset_of_dvd [AddCommMonoidₓ M] [CommMonoidₓ N] {f1 f2 : α →₀ M} {g1 g2 : α → M → N}
    (h1 : f1.Support ⊆ f2.Support) (h2 : ∀ a : α, a ∈ f1.Support → g1 a (f1 a) ∣ g2 a (f2 a)) :
    f1.Prod g1 ∣ f2.Prod g2 := by
  simp only [Finsupp.prod, Finsupp.prod_mul]
  rw [← sdiff_union_of_subset h1, prod_union sdiff_disjoint]
  apply dvd_mul_of_dvd_right
  apply prod_dvd_prod_of_dvd
  exact h2

end Finsupp

theorem Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k i :=
  (Finsupp.applyAddHom i : (ι →₀ A) →+ A).map_sum f s

theorem Finsupp.sum_apply' : g.Sum k x = g.Sum fun i b => k i b x :=
  Finset.sum_apply _ _ _

section

include h0 h1

open Classical

theorem Finsupp.sum_sum_index' : (∑ x in s, f x).Sum t = ∑ x in s, (f x).Sum t :=
  (Finset.induction_on s rfl) fun a s has ih => by
    simp_rw [Finset.sum_insert has, Finsupp.sum_add_index' h0 h1, ih]

end

section

variable [NonUnitalNonAssocSemiringₓ R] [NonUnitalNonAssocSemiringₓ S]

theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} : s.Sum f * b = s.Sum fun a c => f a c * b := by
  simp only [Finsupp.sum, Finset.sum_mul]

theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} : b * s.Sum f = s.Sum fun a c => b * f a c := by
  simp only [Finsupp.sum, Finset.mul_sum]

end

namespace Nat

/-- If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x in f.support, x ^ (f x)`. -/
theorem prod_pow_pos_of_zero_not_mem_support {f : ℕ →₀ ℕ} (hf : 0 ∉ f.Support) : 0 < f.Prod pow :=
  Finset.prod_pos fun a ha =>
    pos_iff_ne_zero.mpr
      (pow_ne_zero _ fun H => by
        subst H
        exact hf ha)

end Nat

