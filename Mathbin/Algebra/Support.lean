/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Module.Pi

/-!
# Support of a function

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `function.mul_support f = {x | f x ≠ 1}`.
-/


open Set

open BigOperators

namespace Function

variable {α β A B M N P R S G M₀ G₀ : Type _} {ι : Sort _}

section One

variable [One M] [One N] [One P]

/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def Support [Zero A] (f : α → A) : Set α :=
  { x | f x ≠ 0 }
#align function.support Function.Support

/-- `mul_support` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive]
def MulSupport (f : α → M) : Set α :=
  { x | f x ≠ 1 }
#align function.mul_support Function.MulSupport

@[to_additive]
theorem mul_support_eq_preimage (f : α → M) : MulSupport f = f ⁻¹' {1}ᶜ :=
  rfl
#align function.mul_support_eq_preimage Function.mul_support_eq_preimage

@[to_additive]
theorem nmem_mul_support {f : α → M} {x : α} : x ∉ MulSupport f ↔ f x = 1 :=
  not_not
#align function.nmem_mul_support Function.nmem_mul_support

@[to_additive]
theorem compl_mul_support {f : α → M} : MulSupport fᶜ = { x | f x = 1 } :=
  ext fun x => nmem_mul_support
#align function.compl_mul_support Function.compl_mul_support

@[simp, to_additive]
theorem mem_mul_support {f : α → M} {x : α} : x ∈ MulSupport f ↔ f x ≠ 1 :=
  Iff.rfl
#align function.mem_mul_support Function.mem_mul_support

@[simp, to_additive]
theorem mul_support_subset_iff {f : α → M} {s : Set α} : MulSupport f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
  Iff.rfl
#align function.mul_support_subset_iff Function.mul_support_subset_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:610:2: warning: expanding binder collection (x «expr ∉ » s) -/
@[to_additive]
theorem mul_support_subset_iff' {f : α → M} {s : Set α} : MulSupport f ⊆ s ↔ ∀ (x) (_ : x ∉ s), f x = 1 :=
  forall_congr' fun x => not_imp_comm
#align function.mul_support_subset_iff' Function.mul_support_subset_iff'

@[to_additive]
theorem mul_support_eq_iff {f : α → M} {s : Set α} : MulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1 :=
  by
  constructor
  · rintro rfl
    simp
    
  · rintro ⟨hs, hsc⟩
    refine' subset.antisymm _ hs
    simp only [mul_support_subset_iff, Ne.def]
    intro x hx
    contrapose! hx
    exact hsc x hx
    
#align function.mul_support_eq_iff Function.mul_support_eq_iff

@[to_additive]
theorem mul_support_disjoint_iff {f : α → M} {s : Set α} : Disjoint (MulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, mul_support_subset_iff', not_mem_compl_iff, eq_on, Pi.one_apply]
#align function.mul_support_disjoint_iff Function.mul_support_disjoint_iff

@[to_additive]
theorem disjoint_mul_support_iff {f : α → M} {s : Set α} : Disjoint s (MulSupport f) ↔ EqOn f 1 s := by
  rw [Disjoint.comm, mul_support_disjoint_iff]
#align function.disjoint_mul_support_iff Function.disjoint_mul_support_iff

@[simp, to_additive]
theorem mul_support_eq_empty_iff {f : α → M} : MulSupport f = ∅ ↔ f = 1 := by
  simp_rw [← subset_empty_iff, mul_support_subset_iff', funext_iff]
  simp
#align function.mul_support_eq_empty_iff Function.mul_support_eq_empty_iff

@[simp, to_additive]
theorem mul_support_nonempty_iff {f : α → M} : (MulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [← ne_empty_iff_nonempty, Ne.def, mul_support_eq_empty_iff]
#align function.mul_support_nonempty_iff Function.mul_support_nonempty_iff

@[to_additive]
theorem range_subset_insert_image_mul_support (f : α → M) : Range f ⊆ insert 1 (f '' MulSupport f) := by
  intro y hy
  rcases eq_or_ne y 1 with (rfl | h2y)
  · exact mem_insert _ _
    
  · obtain ⟨x, rfl⟩ := hy
    refine' mem_insert_of_mem _ ⟨x, h2y, rfl⟩
    
#align function.range_subset_insert_image_mul_support Function.range_subset_insert_image_mul_support

@[simp, to_additive]
theorem mul_support_one' : MulSupport (1 : α → M) = ∅ :=
  mul_support_eq_empty_iff.2 rfl
#align function.mul_support_one' Function.mul_support_one'

@[simp, to_additive]
theorem mul_support_one : (MulSupport fun x : α => (1 : M)) = ∅ :=
  mul_support_one'
#align function.mul_support_one Function.mul_support_one

@[to_additive]
theorem mul_support_const {c : M} (hc : c ≠ 1) : (MulSupport fun x : α => c) = Set.Univ := by
  ext x
  simp [hc]
#align function.mul_support_const Function.mul_support_const

@[to_additive]
theorem mul_support_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : α → M) (g : α → N) :
    (MulSupport fun x => op (f x) (g x)) ⊆ MulSupport f ∪ MulSupport g := fun x hx =>
  Classical.by_cases (fun hf : f x = 1 => Or.inr fun hg => hx <| by simp only [hf, hg, op1]) Or.inl
#align function.mul_support_binop_subset Function.mul_support_binop_subset

@[to_additive]
theorem mul_support_sup [SemilatticeSup M] (f g : α → M) :
    (MulSupport fun x => f x ⊔ g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (· ⊔ ·) sup_idem f g
#align function.mul_support_sup Function.mul_support_sup

@[to_additive]
theorem mul_support_inf [SemilatticeInf M] (f g : α → M) :
    (MulSupport fun x => f x ⊓ g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (· ⊓ ·) inf_idem f g
#align function.mul_support_inf Function.mul_support_inf

@[to_additive]
theorem mul_support_max [LinearOrder M] (f g : α → M) :
    (MulSupport fun x => max (f x) (g x)) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_sup f g
#align function.mul_support_max Function.mul_support_max

@[to_additive]
theorem mul_support_min [LinearOrder M] (f g : α → M) :
    (MulSupport fun x => min (f x) (g x)) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_inf f g
#align function.mul_support_min Function.mul_support_min

@[to_additive]
theorem mul_support_supr [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (MulSupport fun x => ⨆ i, f i x) ⊆ ⋃ i, MulSupport (f i) := by
  rw [mul_support_subset_iff']
  simp only [mem_Union, not_exists, nmem_mul_support]
  intro x hx
  simp only [hx, csupr_const]
#align function.mul_support_supr Function.mul_support_supr

@[to_additive]
theorem mul_support_infi [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (MulSupport fun x => ⨅ i, f i x) ⊆ ⋃ i, MulSupport (f i) :=
  @mul_support_supr _ Mᵒᵈ ι ⟨(1 : M)⟩ _ _ f
#align function.mul_support_infi Function.mul_support_infi

@[to_additive]
theorem mul_support_comp_subset {g : M → N} (hg : g 1 = 1) (f : α → M) : MulSupport (g ∘ f) ⊆ MulSupport f := fun x =>
  mt fun h => by simp only [(· ∘ ·), *]
#align function.mul_support_comp_subset Function.mul_support_comp_subset

@[to_additive]
theorem mul_support_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : α → M) :
    MulSupport f ⊆ MulSupport (g ∘ f) := fun x => mt hg
#align function.mul_support_subset_comp Function.mul_support_subset_comp

@[to_additive]
theorem mul_support_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : α → M) : MulSupport (g ∘ f) = MulSupport f :=
  Set.ext fun x => not_congr hg
#align function.mul_support_comp_eq Function.mul_support_comp_eq

@[to_additive]
theorem mul_support_comp_eq_preimage (g : β → M) (f : α → β) : MulSupport (g ∘ f) = f ⁻¹' MulSupport g :=
  rfl
#align function.mul_support_comp_eq_preimage Function.mul_support_comp_eq_preimage

@[to_additive support_prod_mk]
theorem mul_support_prod_mk (f : α → M) (g : α → N) : (MulSupport fun x => (f x, g x)) = MulSupport f ∪ MulSupport g :=
  Set.ext fun x => by simp only [mul_support, not_and_or, mem_union, mem_set_of_eq, Prod.mk_eq_one, Ne.def]
#align function.mul_support_prod_mk Function.mul_support_prod_mk

@[to_additive support_prod_mk']
theorem mul_support_prod_mk' (f : α → M × N) :
    MulSupport f = (MulSupport fun x => (f x).1) ∪ MulSupport fun x => (f x).2 := by
  simp only [← mul_support_prod_mk, Prod.mk.eta]
#align function.mul_support_prod_mk' Function.mul_support_prod_mk'

@[to_additive]
theorem mul_support_along_fiber_subset (f : α × β → M) (a : α) :
    (MulSupport fun b => f (a, b)) ⊆ (MulSupport f).Image Prod.snd := by tidy
#align function.mul_support_along_fiber_subset Function.mul_support_along_fiber_subset

@[simp, to_additive]
theorem mul_support_along_fiber_finite_of_finite (f : α × β → M) (a : α) (h : (MulSupport f).Finite) :
    (MulSupport fun b => f (a, b)).Finite :=
  (h.Image Prod.snd).Subset (mul_support_along_fiber_subset f a)
#align function.mul_support_along_fiber_finite_of_finite Function.mul_support_along_fiber_finite_of_finite

end One

@[to_additive]
theorem mul_support_mul [MulOneClass M] (f g : α → M) : (MulSupport fun x => f x * g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (· * ·) (one_mul _) f g
#align function.mul_support_mul Function.mul_support_mul

@[to_additive]
theorem mul_support_pow [Monoid M] (f : α → M) (n : ℕ) : (MulSupport fun x => f x ^ n) ⊆ MulSupport f := by
  induction' n with n hfn
  · simpa only [pow_zero, mul_support_one] using empty_subset _
    
  · simpa only [pow_succ] using subset_trans (mul_support_mul f _) (union_subset (subset.refl _) hfn)
    
#align function.mul_support_pow Function.mul_support_pow

section DivisionMonoid

variable [DivisionMonoid G] (f g : α → G)

@[simp, to_additive]
theorem mul_support_inv : (MulSupport fun x => (f x)⁻¹) = MulSupport f :=
  ext fun _ => inv_ne_one
#align function.mul_support_inv Function.mul_support_inv

@[simp, to_additive]
theorem mul_support_inv' : MulSupport f⁻¹ = MulSupport f :=
  mul_support_inv f
#align function.mul_support_inv' Function.mul_support_inv'

@[to_additive]
theorem mul_support_mul_inv : (MulSupport fun x => f x * (g x)⁻¹) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (fun a b => a * b⁻¹) (by simp) f g
#align function.mul_support_mul_inv Function.mul_support_mul_inv

@[to_additive]
theorem mul_support_div : (MulSupport fun x => f x / g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (· / ·) one_div_one f g
#align function.mul_support_div Function.mul_support_div

end DivisionMonoid

theorem support_smul [Zero R] [Zero M] [SmulWithZero R M] [NoZeroSmulDivisors R M] (f : α → R) (g : α → M) :
    Support (f • g) = Support f ∩ Support g :=
  ext fun x => smul_ne_zero_iff
#align function.support_smul Function.support_smul

@[simp]
theorem support_mul [MulZeroClass R] [NoZeroDivisors R] (f g : α → R) :
    (Support fun x => f x * g x) = Support f ∩ Support g :=
  support_smul f g
#align function.support_mul Function.support_mul

@[simp]
theorem support_mul_subset_left [MulZeroClass R] (f g : α → R) : (Support fun x => f x * g x) ⊆ Support f :=
  fun x hfg hf => hfg <| by simp only [hf, zero_mul]
#align function.support_mul_subset_left Function.support_mul_subset_left

@[simp]
theorem support_mul_subset_right [MulZeroClass R] (f g : α → R) : (Support fun x => f x * g x) ⊆ Support g :=
  fun x hfg hg => hfg <| by simp only [hg, mul_zero]
#align function.support_mul_subset_right Function.support_mul_subset_right

theorem support_smul_subset_right [AddMonoid A] [Monoid B] [DistribMulAction B A] (b : B) (f : α → A) :
    Support (b • f) ⊆ Support f := fun x hbf hf => hbf <| by rw [Pi.smul_apply, hf, smul_zero]
#align function.support_smul_subset_right Function.support_smul_subset_right

theorem support_smul_subset_left [Zero M] [Zero β] [SmulWithZero M β] (f : α → M) (g : α → β) :
    Support (f • g) ⊆ Support f := fun x hfg hf => hfg <| by rw [Pi.smul_apply', hf, zero_smul]
#align function.support_smul_subset_left Function.support_smul_subset_left

theorem support_const_smul_of_ne_zero [Semiring R] [AddCommMonoid M] [Module R M] [NoZeroSmulDivisors R M] (c : R)
    (g : α → M) (hc : c ≠ 0) : Support (c • g) = Support g :=
  ext fun x => by simp only [hc, mem_support, Pi.smul_apply, Ne.def, smul_eq_zero, false_or_iff]
#align function.support_const_smul_of_ne_zero Function.support_const_smul_of_ne_zero

@[simp]
theorem support_inv [GroupWithZero G₀] (f : α → G₀) : (Support fun x => (f x)⁻¹) = Support f :=
  Set.ext fun x => not_congr inv_eq_zero
#align function.support_inv Function.support_inv

@[simp]
theorem support_div [GroupWithZero G₀] (f g : α → G₀) : (Support fun x => f x / g x) = Support f ∩ Support g := by
  simp [div_eq_mul_inv]
#align function.support_div Function.support_div

@[to_additive]
theorem mul_support_prod [CommMonoid M] (s : Finset α) (f : α → β → M) :
    (MulSupport fun x => ∏ i in s, f i x) ⊆ ⋃ i ∈ s, MulSupport (f i) := by
  rw [mul_support_subset_iff']
  simp only [mem_Union, not_exists, nmem_mul_support]
  exact fun x => Finset.prod_eq_one
#align function.mul_support_prod Function.mul_support_prod

theorem support_prod_subset [CommMonoidWithZero A] (s : Finset α) (f : α → β → A) :
    (Support fun x => ∏ i in s, f i x) ⊆ ⋂ i ∈ s, Support (f i) := fun x hx =>
  mem_Inter₂.2 fun i hi H => hx <| Finset.prod_eq_zero hi H
#align function.support_prod_subset Function.support_prod_subset

theorem support_prod [CommMonoidWithZero A] [NoZeroDivisors A] [Nontrivial A] (s : Finset α) (f : α → β → A) :
    (Support fun x => ∏ i in s, f i x) = ⋂ i ∈ s, Support (f i) :=
  Set.ext fun x => by simp only [support, Ne.def, Finset.prod_eq_zero_iff, mem_set_of_eq, Set.mem_Inter, not_exists]
#align function.support_prod Function.support_prod

theorem mul_support_one_add [One R] [AddLeftCancelMonoid R] (f : α → R) : (MulSupport fun x => 1 + f x) = Support f :=
  Set.ext fun x => not_congr add_right_eq_self
#align function.mul_support_one_add Function.mul_support_one_add

theorem mul_support_one_add' [One R] [AddLeftCancelMonoid R] (f : α → R) : MulSupport (1 + f) = Support f :=
  mul_support_one_add f
#align function.mul_support_one_add' Function.mul_support_one_add'

theorem mul_support_add_one [One R] [AddRightCancelMonoid R] (f : α → R) : (MulSupport fun x => f x + 1) = Support f :=
  Set.ext fun x => not_congr add_left_eq_self
#align function.mul_support_add_one Function.mul_support_add_one

theorem mul_support_add_one' [One R] [AddRightCancelMonoid R] (f : α → R) : MulSupport (f + 1) = Support f :=
  mul_support_add_one f
#align function.mul_support_add_one' Function.mul_support_add_one'

theorem mul_support_one_sub' [One R] [AddGroup R] (f : α → R) : MulSupport (1 - f) = Support f := by
  rw [sub_eq_add_neg, mul_support_one_add', support_neg']
#align function.mul_support_one_sub' Function.mul_support_one_sub'

theorem mul_support_one_sub [One R] [AddGroup R] (f : α → R) : (MulSupport fun x => 1 - f x) = Support f :=
  mul_support_one_sub' f
#align function.mul_support_one_sub Function.mul_support_one_sub

end Function

namespace Set

open Function

variable {α β M : Type _} [One M] {f : α → M}

@[to_additive]
theorem image_inter_mul_support_eq {s : Set β} {g : β → α} : g '' s ∩ MulSupport f = g '' (s ∩ MulSupport (f ∘ g)) := by
  rw [mul_support_comp_eq_preimage f g, image_inter_preimage]
#align set.image_inter_mul_support_eq Set.image_inter_mul_support_eq

end Set

namespace Pi

variable {A : Type _} {B : Type _} [DecidableEq A] [Zero B] {a : A} {b : B}

theorem support_single_zero : Function.Support (Pi.single a (0 : B)) = ∅ := by simp
#align pi.support_single_zero Pi.support_single_zero

@[simp]
theorem support_single_of_ne (h : b ≠ 0) : Function.Support (Pi.single a b) = {a} := by
  ext
  simp only [mem_singleton_iff, Ne.def, Function.mem_support]
  constructor
  · contrapose!
    exact fun h' => single_eq_of_ne h' b
    
  · rintro rfl
    rw [single_eq_same]
    exact h
    
#align pi.support_single_of_ne Pi.support_single_of_ne

theorem support_single [DecidableEq B] : Function.Support (Pi.single a b) = if b = 0 then ∅ else {a} := by
  split_ifs with h <;> simp [h]
#align pi.support_single Pi.support_single

theorem support_single_subset : Function.Support (Pi.single a b) ⊆ {a} := by classical rw [support_single]
#align pi.support_single_subset Pi.support_single_subset

theorem support_single_disjoint {b' : B} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : A} :
    Disjoint (Function.Support (single i b)) (Function.Support (single j b')) ↔ i ≠ j := by
  rw [support_single_of_ne hb, support_single_of_ne hb', disjoint_singleton]
#align pi.support_single_disjoint Pi.support_single_disjoint

end Pi

