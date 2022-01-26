import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Module.Pi

/-!
# Support of a function

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `function.mul_support f = {x | f x ≠ 1}`.
-/


open Set

open_locale BigOperators

namespace Function

variable {α β A B M N P R S G M₀ G₀ : Type _} {ι : Sort _}

section One

variable [One M] [One N] [One P]

/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def support [Zero A] (f : α → A) : Set α :=
  { x | f x ≠ 0 }

/-- `mul_support` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive]
def mul_support (f : α → M) : Set α :=
  { x | f x ≠ 1 }

@[to_additive]
theorem mul_support_eq_preimage (f : α → M) : mul_support f = f ⁻¹' {1}ᶜ :=
  rfl

@[to_additive]
theorem nmem_mul_support {f : α → M} {x : α} : x ∉ mul_support f ↔ f x = 1 :=
  not_not

@[to_additive]
theorem compl_mul_support {f : α → M} : mul_support fᶜ = { x | f x = 1 } :=
  ext fun x => nmem_mul_support

@[simp, to_additive]
theorem mem_mul_support {f : α → M} {x : α} : x ∈ mul_support f ↔ f x ≠ 1 :=
  Iff.rfl

@[simp, to_additive]
theorem mul_support_subset_iff {f : α → M} {s : Set α} : mul_support f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
  Iff.rfl

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (x «expr ∉ » s)
@[to_additive]
theorem mul_support_subset_iff' {f : α → M} {s : Set α} : mul_support f ⊆ s ↔ ∀ x _ : x ∉ s, f x = 1 :=
  forall_congrₓ fun x => not_imp_comm

@[simp, to_additive]
theorem mul_support_eq_empty_iff {f : α → M} : mul_support f = ∅ ↔ f = 1 := by
  simp_rw [← subset_empty_iff, mul_support_subset_iff', funext_iff]
  simp

@[simp, to_additive]
theorem mul_support_nonempty_iff {f : α → M} : (mul_support f).Nonempty ↔ f ≠ 1 := by
  rw [← ne_empty_iff_nonempty, Ne.def, mul_support_eq_empty_iff]

@[simp, to_additive]
theorem mul_support_one' : mul_support (1 : α → M) = ∅ :=
  mul_support_eq_empty_iff.2 rfl

@[simp, to_additive]
theorem mul_support_one : (mul_support fun x : α => (1 : M)) = ∅ :=
  mul_support_one'

@[to_additive]
theorem mul_support_const {c : M} (hc : c ≠ 1) : (mul_support fun x : α => c) = Set.Univ := by
  ext x
  simp [hc]

@[to_additive]
theorem mul_support_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : α → M) (g : α → N) :
    (mul_support fun x => op (f x) (g x)) ⊆ mul_support f ∪ mul_support g := fun x hx =>
  Classical.by_cases
    (fun hf : f x = 1 =>
      Or.inr fun hg =>
        hx <| by
          simp only [hf, hg, op1])
    Or.inl

@[to_additive]
theorem mul_support_sup [SemilatticeSup M] (f g : α → M) :
    (mul_support fun x => f x⊔g x) ⊆ mul_support f ∪ mul_support g :=
  mul_support_binop_subset (·⊔·) sup_idem f g

@[to_additive]
theorem mul_support_inf [SemilatticeInf M] (f g : α → M) :
    (mul_support fun x => f x⊓g x) ⊆ mul_support f ∪ mul_support g :=
  mul_support_binop_subset (·⊓·) inf_idem f g

@[to_additive]
theorem mul_support_max [LinearOrderₓ M] (f g : α → M) :
    (mul_support fun x => max (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
  mul_support_sup f g

@[to_additive]
theorem mul_support_min [LinearOrderₓ M] (f g : α → M) :
    (mul_support fun x => min (f x) (g x)) ⊆ mul_support f ∪ mul_support g :=
  mul_support_inf f g

@[to_additive]
theorem mul_support_supr [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mul_support fun x => ⨆ i, f i x) ⊆ ⋃ i, mul_support (f i) := by
  rw [mul_support_subset_iff']
  simp only [mem_Union, not_exists, nmem_mul_support]
  intro x hx
  simp only [hx, csupr_const]

@[to_additive]
theorem mul_support_infi [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mul_support fun x => ⨅ i, f i x) ⊆ ⋃ i, mul_support (f i) :=
  @mul_support_supr _ (OrderDual M) ι ⟨(1 : M)⟩ _ _ f

@[to_additive]
theorem mul_support_comp_subset {g : M → N} (hg : g 1 = 1) (f : α → M) : mul_support (g ∘ f) ⊆ mul_support f := fun x =>
  mt fun h => by
    simp only [· ∘ ·, *]

@[to_additive]
theorem mul_support_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : α → M) :
    mul_support f ⊆ mul_support (g ∘ f) := fun x => mt hg

@[to_additive]
theorem mul_support_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : α → M) :
    mul_support (g ∘ f) = mul_support f :=
  Set.ext fun x => not_congr hg

@[to_additive]
theorem mul_support_comp_eq_preimage (g : β → M) (f : α → β) : mul_support (g ∘ f) = f ⁻¹' mul_support g :=
  rfl

@[to_additive support_prod_mk]
theorem mul_support_prod_mk (f : α → M) (g : α → N) :
    (mul_support fun x => (f x, g x)) = mul_support f ∪ mul_support g :=
  Set.ext fun x => by
    simp only [mul_support, not_and_distrib, mem_union_eq, mem_set_of_eq, Prod.mk_eq_one, Ne.def]

@[to_additive support_prod_mk']
theorem mul_support_prod_mk' (f : α → M × N) :
    mul_support f = (mul_support fun x => (f x).1) ∪ mul_support fun x => (f x).2 := by
  simp only [← mul_support_prod_mk, Prod.mk.eta]

@[to_additive]
theorem mul_support_along_fiber_subset (f : α × β → M) (a : α) :
    (mul_support fun b => f (a, b)) ⊆ (mul_support f).Image Prod.snd := by
  tidy

@[simp, to_additive]
theorem mul_support_along_fiber_finite_of_finite (f : α × β → M) (a : α) (h : (mul_support f).Finite) :
    (mul_support fun b => f (a, b)).Finite :=
  (h.image Prod.snd).Subset (mul_support_along_fiber_subset f a)

end One

@[to_additive]
theorem mul_support_mul [Monoidₓ M] (f g : α → M) : (mul_support fun x => f x * g x) ⊆ mul_support f ∪ mul_support g :=
  mul_support_binop_subset (· * ·) (one_mulₓ _) f g

@[simp, to_additive]
theorem mul_support_inv [Groupₓ G] (f : α → G) : (mul_support fun x => (f x)⁻¹) = mul_support f :=
  Set.ext fun x => not_congr inv_eq_one

@[simp, to_additive]
theorem mul_support_inv' [Groupₓ G] (f : α → G) : mul_support f⁻¹ = mul_support f :=
  mul_support_inv f

@[simp]
theorem mul_support_inv₀ [GroupWithZeroₓ G₀] (f : α → G₀) : (mul_support fun x => (f x)⁻¹) = mul_support f :=
  Set.ext fun x => not_congr inv_eq_one₀

@[to_additive]
theorem mul_support_mul_inv [Groupₓ G] (f g : α → G) :
    (mul_support fun x => f x * (g x)⁻¹) ⊆ mul_support f ∪ mul_support g :=
  mul_support_binop_subset (fun a b => a * b⁻¹)
    (by
      simp )
    f g

@[to_additive support_sub]
theorem mul_support_group_div [Groupₓ G] (f g : α → G) :
    (mul_support fun x => f x / g x) ⊆ mul_support f ∪ mul_support g :=
  mul_support_binop_subset (· / ·)
    (by
      simp only [one_div, one_inv])
    f g

theorem mul_support_div [GroupWithZeroₓ G₀] (f g : α → G₀) :
    (mul_support fun x => f x / g x) ⊆ mul_support f ∪ mul_support g :=
  mul_support_binop_subset (· / ·)
    (by
      simp only [div_one])
    f g

@[simp]
theorem support_mul [MulZeroClass R] [NoZeroDivisors R] (f g : α → R) :
    (support fun x => f x * g x) = support f ∩ support g :=
  Set.ext fun x => by
    simp only [mem_support, mul_ne_zero_iff, mem_inter_eq, not_or_distrib]

theorem support_smul_subset_right [AddMonoidₓ A] [Monoidₓ B] [DistribMulAction B A] (b : B) (f : α → A) :
    support (b • f) ⊆ support f := fun x hbf hf =>
  hbf <| by
    rw [Pi.smul_apply, hf, smul_zero]

theorem support_smul_subset_left [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support f := fun x hfg hf =>
  hfg <| by
    rw [Pi.smul_apply', hf, zero_smul]

theorem support_smul [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [NoZeroSmulDivisors R M] (f : α → R) (g : α → M) :
    support (f • g) = support f ∩ support g :=
  ext fun x => smul_ne_zero

@[simp]
theorem support_inv [GroupWithZeroₓ G₀] (f : α → G₀) : (support fun x => (f x)⁻¹) = support f :=
  Set.ext fun x => not_congr inv_eq_zero

@[simp]
theorem support_div [GroupWithZeroₓ G₀] (f g : α → G₀) : (support fun x => f x / g x) = support f ∩ support g := by
  simp [div_eq_mul_inv]

@[to_additive]
theorem mul_support_prod [CommMonoidₓ M] (s : Finset α) (f : α → β → M) :
    (mul_support fun x => ∏ i in s, f i x) ⊆ ⋃ i ∈ s, mul_support (f i) := by
  rw [mul_support_subset_iff']
  simp only [mem_Union, not_exists, nmem_mul_support]
  exact fun x => Finset.prod_eq_one

theorem support_prod_subset [CommMonoidWithZero A] (s : Finset α) (f : α → β → A) :
    (support fun x => ∏ i in s, f i x) ⊆ ⋂ i ∈ s, support (f i) := fun x hx =>
  mem_Inter₂.2 fun i hi H => hx <| Finset.prod_eq_zero hi H

theorem support_prod [CommMonoidWithZero A] [NoZeroDivisors A] [Nontrivial A] (s : Finset α) (f : α → β → A) :
    (support fun x => ∏ i in s, f i x) = ⋂ i ∈ s, support (f i) :=
  Set.ext fun x => by
    simp only [support, Ne.def, Finset.prod_eq_zero_iff, mem_set_of_eq, Set.mem_Inter, not_exists]

theorem mul_support_one_add [One R] [AddLeftCancelMonoid R] (f : α → R) : (mul_support fun x => 1 + f x) = support f :=
  Set.ext fun x => not_congr add_right_eq_selfₓ

theorem mul_support_one_add' [One R] [AddLeftCancelMonoid R] (f : α → R) : mul_support (1 + f) = support f :=
  mul_support_one_add f

theorem mul_support_add_one [One R] [AddRightCancelMonoid R] (f : α → R) : (mul_support fun x => f x + 1) = support f :=
  Set.ext fun x => not_congr add_left_eq_self

theorem mul_support_add_one' [One R] [AddRightCancelMonoid R] (f : α → R) : mul_support (f + 1) = support f :=
  mul_support_add_one f

theorem mul_support_one_sub' [One R] [AddGroupₓ R] (f : α → R) : mul_support (1 - f) = support f := by
  rw [sub_eq_add_neg, mul_support_one_add', support_neg']

theorem mul_support_one_sub [One R] [AddGroupₓ R] (f : α → R) : (mul_support fun x => 1 - f x) = support f :=
  mul_support_one_sub' f

end Function

namespace Set

open Function

variable {α β M : Type _} [One M] {f : α → M}

@[to_additive]
theorem image_inter_mul_support_eq {s : Set β} {g : β → α} : g '' s ∩ mul_support f = g '' (s ∩ mul_support (f ∘ g)) :=
  by
  rw [mul_support_comp_eq_preimage f g, image_inter_preimage]

end Set

namespace Pi

variable {A : Type _} {B : Type _} [DecidableEq A] [Zero B] {a : A} {b : B}

theorem support_single_zero : Function.Support (Pi.single a (0 : B)) = ∅ := by
  simp

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
    

theorem support_single [DecidableEq B] : Function.Support (Pi.single a b) = if b = 0 then ∅ else {a} := by
  split_ifs with h <;> simp [h]

theorem support_single_subset : Function.Support (Pi.single a b) ⊆ {a} := by
  classical
  rw [support_single]
  split_ifs <;> simp

theorem support_single_disjoint {b' : B} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : A} :
    Disjoint (Function.Support (single i b)) (Function.Support (single j b')) ↔ i ≠ j := by
  rw [support_single_of_ne hb, support_single_of_ne hb', disjoint_singleton]

end Pi

