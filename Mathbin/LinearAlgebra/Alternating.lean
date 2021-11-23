import Mathbin.LinearAlgebra.Multilinear.Basis 
import Mathbin.LinearAlgebra.Multilinear.TensorProduct 
import Mathbin.LinearAlgebra.LinearIndependent 
import Mathbin.GroupTheory.Perm.Sign 
import Mathbin.GroupTheory.Perm.Subgroup 
import Mathbin.Data.Equiv.Fin 
import Mathbin.GroupTheory.QuotientGroup

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `module` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.
* `multilinear_map.alternatization`, which makes an alternating map out of a non-alternating one.
* `alternating_map.dom_coprod`, which behaves as a product between two alternating maps.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.

`alternating_map`s are provided with a coercion to `multilinear_map`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `alternating_map.coe_add`
* `alternating_map.coe_zero`
* `alternating_map.coe_sub`
* `alternating_map.coe_neg`
* `alternating_map.coe_smul`
-/


variable{R : Type _}[Semiringₓ R]

variable{M : Type _}[AddCommMonoidₓ M][Module R M]

variable{N : Type _}[AddCommMonoidₓ N][Module R N]

variable{M' : Type _}[AddCommGroupₓ M'][Module R M']

variable{N' : Type _}[AddCommGroupₓ N'][Module R N']

variable{ι : Type _}[DecidableEq ι]

section 

variable(R M N ι)

/--
An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure AlternatingMap extends MultilinearMap R (fun i : ι => M) N where 
  map_eq_zero_of_eq' : ∀ v : ι → M i j : ι h : v i = v j hij : i ≠ j, to_fun v = 0

end 

/-- The multilinear map associated to an alternating map -/
add_decl_doc AlternatingMap.toMultilinearMap

namespace AlternatingMap

variable(f f' : AlternatingMap R M N ι)

variable(g g₂ : AlternatingMap R M N' ι)

variable(g' : AlternatingMap R M' N' ι)

variable(v : ι → M)(v' : ι → M')

open Function

/-! Basic coercion simp lemmas, largely copied from `ring_hom` and `multilinear_map` -/


section Coercions

instance  : CoeFun (AlternatingMap R M N ι) fun _ => (ι → M) → N :=
  ⟨fun x => x.to_fun⟩

initialize_simps_projections AlternatingMap (toFun → apply)

@[simp]
theorem to_fun_eq_coe : f.to_fun = f :=
  rfl

@[simp]
theorem coe_mk (f : (ι → M) → N) h₁ h₂ h₃ : «expr⇑ » (⟨f, h₁, h₂, h₃⟩ : AlternatingMap R M N ι) = f :=
  rfl

theorem congr_funₓ {f g : AlternatingMap R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
  congr_argₓ (fun h : AlternatingMap R M N ι => h x) h

theorem congr_argₓ (f : AlternatingMap R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
  congr_argₓ (fun x : ι → M => f x) h

theorem coe_injective : injective (coeFn : AlternatingMap R M N ι → (ι → M) → N) :=
  fun f g h =>
    by 
      cases f 
      cases g 
      cases h 
      rfl

@[simp, normCast]
theorem coe_inj {f g : AlternatingMap R M N ι} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext {f f' : AlternatingMap R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
  coe_injective (funext H)

theorem ext_iff {f g : AlternatingMap R M N ι} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

instance  : Coe (AlternatingMap R M N ι) (MultilinearMap R (fun i : ι => M) N) :=
  ⟨fun x => x.to_multilinear_map⟩

@[simp, normCast]
theorem coe_multilinear_map : «expr⇑ » (f : MultilinearMap R (fun i : ι => M) N) = f :=
  rfl

theorem coe_multilinear_map_injective :
  Function.Injective (coeₓ : AlternatingMap R M N ι → MultilinearMap R (fun i : ι => M) N) :=
  fun x y h => ext$ MultilinearMap.congr_fun h

@[simp]
theorem to_multilinear_map_eq_coe : f.to_multilinear_map = f :=
  rfl

@[simp]
theorem coe_multilinear_map_mk (f : (ι → M) → N) h₁ h₂ h₃ :
  ((⟨f, h₁, h₂, h₃⟩ : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = ⟨f, h₁, h₂⟩ :=
  rfl

end Coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.to_fun`.
-/


@[simp]
theorem map_add (i : ι) (x y : M) : f (update v i (x+y)) = f (update v i x)+f (update v i y) :=
  f.to_multilinear_map.map_add' v i x y

@[simp]
theorem map_sub (i : ι) (x y : M') : g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
  g'.to_multilinear_map.map_sub v' i x y

@[simp]
theorem map_neg (i : ι) (x : M') : g' (update v' i (-x)) = -g' (update v' i x) :=
  g'.to_multilinear_map.map_neg v' i x

@[simp]
theorem map_smul (i : ι) (r : R) (x : M) : f (update v i (r • x)) = r • f (update v i x) :=
  f.to_multilinear_map.map_smul' v i r x

@[simp]
theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.to_multilinear_map.map_coord_zero i h

@[simp]
theorem map_update_zero (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.to_multilinear_map.map_update_zero m i

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.to_multilinear_map.map_zero

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 :=
  by 
    rw [Function.Injective] at hv 
    pushNeg  at hv 
    rcases hv with ⟨i₁, i₂, heq, hne⟩
    exact f.map_eq_zero_of_eq v HEq hne

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `module` structure
as `multilinear_map`
-/


instance  : Add (AlternatingMap R M N ι) :=
  ⟨fun a b =>
      { (a+b : MultilinearMap R (fun i : ι => M) N) with
        map_eq_zero_of_eq' :=
          fun v i j h hij =>
            by 
              simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem add_apply : (f+f') v = f v+f' v :=
  rfl

@[normCast]
theorem coe_add : («expr↑ » (f+f') : MultilinearMap R (fun i : ι => M) N) = f+f' :=
  rfl

instance  : HasZero (AlternatingMap R M N ι) :=
  ⟨{ (0 : MultilinearMap R (fun i : ι => M) N) with
      map_eq_zero_of_eq' :=
        fun v i j h hij =>
          by 
            simp  }⟩

@[simp]
theorem zero_apply : (0 : AlternatingMap R M N ι) v = 0 :=
  rfl

@[normCast]
theorem coe_zero : ((0 : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = 0 :=
  rfl

instance  : Inhabited (AlternatingMap R M N ι) :=
  ⟨0⟩

instance  : AddCommMonoidₓ (AlternatingMap R M N ι) :=
  { zero := 0, add := ·+·,
    zero_add :=
      by 
        intros  <;> ext <;> simp [add_commₓ, add_left_commₓ],
    add_zero :=
      by 
        intros  <;> ext <;> simp [add_commₓ, add_left_commₓ],
    add_comm :=
      by 
        intros  <;> ext <;> simp [add_commₓ, add_left_commₓ],
    add_assoc :=
      by 
        intros  <;> ext <;> simp [add_commₓ, add_left_commₓ],
    nsmul :=
      fun n f =>
        { (n • f : MultilinearMap R (fun i : ι => M) N) with
          map_eq_zero_of_eq' :=
            fun v i j h hij =>
              by 
                simp [f.map_eq_zero_of_eq v h hij] },
    nsmul_zero' :=
      by 
        intros 
        ext 
        simp [add_smul],
    nsmul_succ' :=
      by 
        intros 
        ext 
        simp [add_smul, Nat.succ_eq_one_add] }

instance  : Neg (AlternatingMap R M N' ι) :=
  ⟨fun f =>
      { -(f : MultilinearMap R (fun i : ι => M) N') with
        map_eq_zero_of_eq' :=
          fun v i j h hij =>
            by 
              simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl

@[normCast]
theorem coe_neg : ((-g : AlternatingMap R M N' ι) : MultilinearMap R (fun i : ι => M) N') = -g :=
  rfl

instance  : Sub (AlternatingMap R M N' ι) :=
  ⟨fun f g =>
      { (f - g : MultilinearMap R (fun i : ι => M) N') with
        map_eq_zero_of_eq' :=
          fun v i j h hij =>
            by 
              simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl

@[normCast]
theorem coe_sub : («expr↑ » (g - g₂) : MultilinearMap R (fun i : ι => M) N') = g - g₂ :=
  rfl

instance  : AddCommGroupₓ (AlternatingMap R M N' ι) :=
  by 
    refine'
        { AlternatingMap.addCommMonoid with zero := 0, add := ·+·, neg := Neg.neg, sub := Sub.sub, sub_eq_add_neg := _,
          nsmul :=
            fun n f =>
              { (n • f : MultilinearMap R (fun i : ι => M) N') with
                map_eq_zero_of_eq' :=
                  fun v i j h hij =>
                    by 
                      simp [f.map_eq_zero_of_eq v h hij] },
          zsmul :=
            fun n f =>
              { (n • f : MultilinearMap R (fun i : ι => M) N') with
                map_eq_zero_of_eq' :=
                  fun v i j h hij =>
                    by 
                      simp [f.map_eq_zero_of_eq v h hij] },
          zsmul_zero' := _, zsmul_succ' := _, zsmul_neg' := _, .. } <;>
      intros  <;> ext <;> simp [add_commₓ, add_left_commₓ, sub_eq_add_neg, add_smul, Nat.succ_eq_add_one, coe_nat_zsmul]

section DistribMulAction

variable{S : Type _}[Monoidₓ S][DistribMulAction S N][SmulCommClass R S N]

instance  : HasScalar S (AlternatingMap R M N ι) :=
  ⟨fun c f =>
      { (c • f : MultilinearMap R (fun i : ι => M) N) with
        map_eq_zero_of_eq' :=
          fun v i j h hij =>
            by 
              simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl

@[normCast]
theorem coe_smul (c : S) : ((c • f : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = c • f :=
  rfl

theorem coe_fn_smul (c : S) (f : AlternatingMap R M N ι) : «expr⇑ » (c • f) = c • f :=
  rfl

instance  : DistribMulAction S (AlternatingMap R M N ι) :=
  { one_smul := fun f => ext$ fun x => one_smul _ _, mul_smul := fun c₁ c₂ f => ext$ fun x => mul_smul _ _ _,
    smul_zero := fun r => ext$ fun x => smul_zero _, smul_add := fun r f₁ f₂ => ext$ fun x => smul_add _ _ _ }

end DistribMulAction

section Module

variable{S : Type _}[Semiringₓ S][Module S N][SmulCommClass R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance  : Module S (AlternatingMap R M N ι) :=
  { add_smul := fun r₁ r₂ f => ext$ fun x => add_smul _ _ _, zero_smul := fun f => ext$ fun x => zero_smul _ _ }

instance  [NoZeroSmulDivisors S N] : NoZeroSmulDivisors S (AlternatingMap R M N ι) :=
  coe_injective.NoZeroSmulDivisors _ rfl coe_fn_smul

end Module

section 

variable(R N)

/-- The evaluation map from `ι → N` to `N` at a given `i` is alternating when `ι` is subsingleton.
-/
@[simps]
def of_subsingleton [Subsingleton ι] (i : ι) : AlternatingMap R N N ι :=
  { MultilinearMap.ofSubsingleton R N i with toFun := Function.eval i,
    map_eq_zero_of_eq' := fun v i j hv hij => (hij$ Subsingleton.elimₓ _ _).elim }

end 

end AlternatingMap

/-!
### Composition with linear maps
-/


namespace LinearMap

variable{N₂ : Type _}[AddCommMonoidₓ N₂][Module R N₂]

/-- Composing a alternating map with a linear map on the left gives again an alternating map. -/
def comp_alternating_map (g : N →ₗ[R] N₂) : AlternatingMap R M N ι →+ AlternatingMap R M N₂ ι :=
  { toFun :=
      fun f =>
        { g.comp_multilinear_map (f : MultilinearMap R (fun _ : ι => M) N) with
          map_eq_zero_of_eq' :=
            fun v i j h hij =>
              by 
                simp [f.map_eq_zero_of_eq v h hij] },
    map_zero' :=
      by 
        ext 
        simp ,
    map_add' :=
      fun a b =>
        by 
          ext 
          simp  }

@[simp]
theorem coe_comp_alternating_map (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) :
  «expr⇑ » (g.comp_alternating_map f) = g ∘ f :=
  rfl

theorem comp_alternating_map_apply (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) (m : ι → M) :
  g.comp_alternating_map f m = g (f m) :=
  rfl

end LinearMap

namespace AlternatingMap

variable{M₂ : Type _}[AddCommMonoidₓ M₂][Module R M₂]

/-- Composing a alternating map with the same linear map on each argument gives again an
alternating map. -/
def comp_linear_map (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) : AlternatingMap R M₂ N ι :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun v i j h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }

theorem coe_comp_linear_map (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) :
  «expr⇑ » (f.comp_linear_map g) = f ∘ (· ∘ ·) g :=
  rfl

@[simp]
theorem comp_linear_map_apply (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
  f.comp_linear_map g v = f fun i => g (v i) :=
  rfl

@[simp]
theorem zero_comp_linear_map (g : M₂ →ₗ[R] M) : (0 : AlternatingMap R M N ι).compLinearMap g = 0 :=
  by 
    ext 
    simp only [comp_linear_map_apply, zero_apply]

@[simp]
theorem add_comp_linear_map (f₁ f₂ : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) :
  (f₁+f₂).compLinearMap g = f₁.comp_linear_map g+f₂.comp_linear_map g :=
  by 
    ext 
    simp only [comp_linear_map_apply, add_apply]

@[simp]
theorem comp_linear_map_zero [Nonempty ι] (f : AlternatingMap R M N ι) : f.comp_linear_map (0 : M₂ →ₗ[R] M) = 0 :=
  by 
    ext 
    simpRw [comp_linear_map_apply, LinearMap.zero_apply, ←Pi.zero_def, map_zero, zero_apply]

variable(f f' : AlternatingMap R M N ι)

variable(g g₂ : AlternatingMap R M N' ι)

variable(g' : AlternatingMap R M' N' ι)

variable(v : ι → M)(v' : ι → M')

open Function

/-!
### Other lemmas from `multilinear_map`
-/


section 

open_locale BigOperators

theorem map_update_sum {α : Type _} (t : Finset α) (i : ι) (g : α → M) (m : ι → M) :
  f (update m i (∑a in t, g a)) = ∑a in t, f (update m i (g a)) :=
  f.to_multilinear_map.map_update_sum t i g m

end 

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`alternating_map.map_eq_zero_of_eq`.
-/


theorem map_update_self {i j : ι} (hij : i ≠ j) : f (Function.update v i (v j)) = 0 :=
  f.map_eq_zero_of_eq _
    (by 
      rw [Function.update_same, Function.update_noteq hij.symm])
    hij

theorem map_update_update {i j : ι} (hij : i ≠ j) (m : M) : f (Function.update (Function.update v i m) j m) = 0 :=
  f.map_eq_zero_of_eq _
    (by 
      rw [Function.update_same, Function.update_noteq hij, Function.update_same])
    hij

theorem map_swap_add {i j : ι} (hij : i ≠ j) : (f (v ∘ Equiv.swap i j)+f v) = 0 :=
  by 
    rw [Equiv.comp_swap_eq_update]
    convert f.map_update_update v hij (v i+v j)
    simp [f.map_update_self _ hij, f.map_update_self _ hij.symm, Function.update_comm hij (v i+v j) (v _) v,
      Function.update_comm hij.symm (v i) (v i) v]

theorem map_add_swap {i j : ι} (hij : i ≠ j) : (f v+f (v ∘ Equiv.swap i j)) = 0 :=
  by 
    rw [add_commₓ]
    exact f.map_swap_add v hij

theorem map_swap {i j : ι} (hij : i ≠ j) : g (v ∘ Equiv.swap i j) = -g v :=
  eq_neg_of_add_eq_zero (g.map_swap_add v hij)

theorem map_perm [Fintype ι] (v : ι → M) (σ : Equiv.Perm ι) : g (v ∘ σ) = σ.sign • g v :=
  by 
    apply Equiv.Perm.swap_induction_on' σ
    ·
      simp 
    ·
      intro s x y hxy hI 
      simpa [g.map_swap (v ∘ s) hxy, Equiv.Perm.sign_swap hxy] using hI

theorem map_congr_perm [Fintype ι] (σ : Equiv.Perm ι) : g v = σ.sign • g (v ∘ σ) :=
  by 
    rw [g.map_perm, smul_smul]
    simp 

theorem coe_dom_dom_congr [Fintype ι] (σ : Equiv.Perm ι) :
  (g : MultilinearMap R (fun _ : ι => M) N').domDomCongr σ = σ.sign • (g : MultilinearMap R (fun _ : ι => M) N') :=
  MultilinearMap.ext$ fun v => g.map_perm v σ

/-- If the arguments are linearly dependent then the result is `0`. -/
theorem map_linear_dependent {K : Type _} [Ringₓ K] {M : Type _} [AddCommGroupₓ M] [Module K M] {N : Type _}
  [AddCommGroupₓ N] [Module K N] [NoZeroSmulDivisors K N] (f : AlternatingMap K M N ι) (v : ι → M)
  (h : ¬LinearIndependent K v) : f v = 0 :=
  by 
    obtain ⟨s, g, h, i, hi, hz⟩ := linear_dependent_iff.mp h 
    suffices  : f (update v i (g i • v i)) = 0
    ·
      rw [f.map_smul, Function.update_eq_self, smul_eq_zero] at this 
      exact Or.resolve_left this hz 
    conv  at h in g _ • v _ => rw [←if_t_t (i = x) (g _ • v _)]
    rw [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, if_pos hi, Finset.sum_singleton, add_eq_zero_iff_eq_neg] at
      h 
    rw [h, f.map_neg, f.map_update_sum, neg_eq_zero, Finset.sum_eq_zero]
    intro j hj 
    obtain ⟨hij, _⟩ := finset.mem_erase.mp hj 
    rw [f.map_smul, f.map_update_self _ hij.symm, smul_zero]

end AlternatingMap

open_locale BigOperators

namespace MultilinearMap

open Equiv

variable[Fintype ι]

private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun i : ι => M) N') (v : ι → M) (i j : ι)
  (i_ne_j : i ≠ j) (hv : v i = v j) : (∑σ : perm ι, σ.sign • m.dom_dom_congr σ) v = 0 :=
  by 
    rw [sum_apply]
    exact
      Finset.sum_involution (fun σ _ => swap i j*σ)
        (fun σ _ =>
          by 
            simp [perm.sign_swap i_ne_j, apply_swap_eq_self hv])
        (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
        fun σ _ => swap_mul_involutive i j σ

/-- Produce an `alternating_map` out of a `multilinear_map`, by summing over all argument
permutations. -/
def alternatization : MultilinearMap R (fun i : ι => M) N' →+ AlternatingMap R M N' ι :=
  { toFun :=
      fun m =>
        { ∑σ : perm ι, σ.sign • m.dom_dom_congr σ with toFun := «expr⇑ » (∑σ : perm ι, σ.sign • m.dom_dom_congr σ),
          map_eq_zero_of_eq' := fun v i j hvij hij => alternization_map_eq_zero_of_eq_aux m v i j hij hvij },
    map_add' :=
      fun a b =>
        by 
          ext 
          simp only [Finset.sum_add_distrib, smul_add, add_apply, dom_dom_congr_apply, AlternatingMap.add_apply,
            AlternatingMap.coe_mk, smul_apply, sum_apply],
    map_zero' :=
      by 
        ext 
        simp only [Finset.sum_const_zero, smul_zero, zero_apply, dom_dom_congr_apply, AlternatingMap.zero_apply,
          AlternatingMap.coe_mk, smul_apply, sum_apply] }

theorem alternatization_def (m : MultilinearMap R (fun i : ι => M) N') :
  «expr⇑ » (alternatization m) = (∑σ : perm ι, σ.sign • m.dom_dom_congr σ : _) :=
  rfl

theorem alternatization_coe (m : MultilinearMap R (fun i : ι => M) N') :
  «expr↑ » m.alternatization = (∑σ : perm ι, σ.sign • m.dom_dom_congr σ : _) :=
  coe_injective rfl

theorem alternatization_apply (m : MultilinearMap R (fun i : ι => M) N') (v : ι → M) :
  alternatization m v = ∑σ : perm ι, σ.sign • m.dom_dom_congr σ v :=
  by 
    simp only [alternatization_def, smul_apply, sum_apply]

end MultilinearMap

namespace AlternatingMap

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
theorem coe_alternatization [Fintype ι] (a : AlternatingMap R M N' ι) :
  («expr↑ » a : MultilinearMap R (fun ι => M) N').alternatization = Nat.factorial (Fintype.card ι) • a :=
  by 
    apply AlternatingMap.coe_injective 
    simpRw [MultilinearMap.alternatization_def, coe_dom_dom_congr, smul_smul, Int.units_mul_self, one_smul,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, ←coe_multilinear_map, coe_smul]

end AlternatingMap

namespace LinearMap

variable{N'₂ : Type _}[AddCommGroupₓ N'₂][Module R N'₂][Fintype ι]

/-- Composition with a linear map before and after alternatization are equivalent. -/
theorem comp_multilinear_map_alternatization (g : N' →ₗ[R] N'₂) (f : MultilinearMap R (fun _ : ι => M) N') :
  (g.comp_multilinear_map f).alternatization = g.comp_alternating_map f.alternatization :=
  by 
    ext 
    simp [MultilinearMap.alternatization_def]

end LinearMap

section Coprod

open_locale BigOperators

open_locale TensorProduct

variable{ιa ιb : Type _}[DecidableEq ιa][DecidableEq ιb][Fintype ιa][Fintype ιb]

variable{R' :
    Type
      _}{Mᵢ N₁ N₂ :
    Type
      _}[CommSemiringₓ
      R'][AddCommGroupₓ N₁][Module R' N₁][AddCommGroupₓ N₂][Module R' N₂][AddCommMonoidₓ Mᵢ][Module R' Mᵢ]

namespace Equiv.Perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β  -/
abbrev mod_sum_congr (α β : Type _) :=
  QuotientGroup.Quotient (Equiv.Perm.sumCongrHom α β).range

theorem mod_sum_congr.swap_smul_involutive {α β : Type _} [DecidableEq (Sum α β)] (i j : Sum α β) :
  Function.Involutive (HasScalar.smul (Equiv.swap i j) : mod_sum_congr α β → mod_sum_congr α β) :=
  fun σ =>
    by 
      apply σ.induction_on' fun σ => _ 
      exact _root_.congr_arg Quotientₓ.mk' (Equiv.swap_mul_involutive i j σ)

end Equiv.Perm

namespace AlternatingMap

open Equiv

-- error in LinearAlgebra.Alternating: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- summand used in `alternating_map.dom_coprod` -/
def dom_coprod.summand
(a : alternating_map R' Mᵢ N₁ ιa)
(b : alternating_map R' Mᵢ N₂ ιb)
(σ : perm.mod_sum_congr ιa ιb) : multilinear_map R' (λ _ : «expr ⊕ »(ιa, ιb), Mᵢ) «expr ⊗[ ] »(N₁, R', N₂) :=
quotient.lift_on' σ (λ
 σ, «expr • »(σ.sign, (multilinear_map.dom_coprod «expr↑ »(a) «expr↑ »(b) : multilinear_map R' (λ
   _, Mᵢ) «expr ⊗ »(N₁, N₂)).dom_dom_congr σ)) (λ (σ₁ σ₂) ⟨⟨sl, sr⟩, h⟩, begin
   ext [] [ident v] [],
   simp [] [] ["only"] ["[", expr multilinear_map.dom_dom_congr_apply, ",", expr multilinear_map.dom_coprod_apply, ",", expr coe_multilinear_map, ",", expr multilinear_map.smul_apply, "]"] [] [],
   replace [ident h] [] [":=", expr inv_mul_eq_iff_eq_mul.mp h.symm],
   have [] [":", expr «expr = »(«expr * »(σ₁, perm.sum_congr_hom _ _ (sl, sr)).sign, «expr * »(σ₁.sign, «expr * »(sl.sign, sr.sign)))] [":=", expr by simp [] [] [] [] [] []],
   rw ["[", expr h, ",", expr this, ",", expr mul_smul, ",", expr mul_smul, ",", expr smul_left_cancel_iff, ",", "<-", expr tensor_product.tmul_smul, ",", expr tensor_product.smul_tmul', "]"] [],
   simp [] [] ["only"] ["[", expr sum.map_inr, ",", expr perm.sum_congr_hom_apply, ",", expr perm.sum_congr_apply, ",", expr sum.map_inl, ",", expr function.comp_app, ",", expr perm.coe_mul, "]"] [] [],
   rw ["[", "<-", expr a.map_congr_perm (λ i, v (σ₁ _)), ",", "<-", expr b.map_congr_perm (λ i, v (σ₁ _)), "]"] []
 end)

theorem dom_coprod.summand_mk' (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
  (σ : Equiv.Perm (Sum ιa ιb)) :
  dom_coprod.summand a b (Quotientₓ.mk' σ) =
    σ.sign •
      (MultilinearMap.domCoprod («expr↑ » a) («expr↑ » b) : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ :=
  rfl

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
theorem dom_coprod.summand_add_swap_smul_eq_zero (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
  (σ : perm.mod_sum_congr ιa ιb) {v : Sum ιa ιb → Mᵢ} {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
  (dom_coprod.summand a b σ v+dom_coprod.summand a b (swap i j • σ) v) = 0 :=
  by 
    apply σ.induction_on' fun σ => _ 
    dsimp only [Quotientₓ.lift_on'_mk', Quotientₓ.map'_mk', MulAction.quotient.smul_mk, dom_coprod.summand]
    rw [perm.sign_mul, perm.sign_swap hij]
    simp only [one_mulₓ, Units.neg_mul, Function.comp_app, Units.neg_smul, perm.coe_mul, Units.coe_neg,
      MultilinearMap.smul_apply, MultilinearMap.neg_apply, MultilinearMap.dom_dom_congr_apply,
      MultilinearMap.dom_coprod_apply]
    convert add_right_negₓ _ <;>
      ·
        ext k 
        rw [Equiv.apply_swap_eq_self hv]

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
theorem dom_coprod.summand_eq_zero_of_smul_invariant (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
  (σ : perm.mod_sum_congr ιa ιb) {v : Sum ιa ιb → Mᵢ} {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
  swap i j • σ = σ → dom_coprod.summand a b σ v = 0 :=
  by 
    apply σ.induction_on' fun σ => _ 
    dsimp only [Quotientₓ.lift_on'_mk', Quotientₓ.map'_mk', MultilinearMap.smul_apply,
      MultilinearMap.dom_dom_congr_apply, MultilinearMap.dom_coprod_apply, dom_coprod.summand]
    intro hσ 
    withCases 
      cases hi : (σ⁻¹) i <;> cases hj : (σ⁻¹) j <;> rw [perm.inv_eq_iff_eq] at hi hj <;> substs hi hj 
    case' [Sum.inl, Sum.inr : i' j', Sum.inr, Sum.inl : i' j'] => 
      all_goals 
        obtain ⟨⟨sl, sr⟩, hσ⟩ := Quotientₓ.exact' hσ 
      workOnGoal 0
        replace hσ := Equiv.congr_fun hσ (Sum.inl i')
      workOnGoal 1
        replace hσ := Equiv.congr_fun hσ (Sum.inr i')
      all_goals 
        rw [←Equiv.mul_swap_eq_swap_mul, mul_inv_rev, Equiv.swap_inv, inv_mul_cancel_right] at hσ 
        simpa using hσ 
    case' [Sum.inr, Sum.inr : i' j', Sum.inl, Sum.inl : i' j'] => 
      all_goals 
        convert smul_zero _ 
      workOnGoal 0
        convert TensorProduct.tmul_zero _ _ 
      workOnGoal 1
        convert TensorProduct.zero_tmul _ _ 
      all_goals 
        exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)

/-- Like `multilinear_map.dom_coprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = fin n` and `ιb = fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `sum`

The specialized version can be obtained by combining this definition with `fin_sum_fin_equiv` and
`algebra.lmul'`.
-/
@[simps]
def dom_coprod (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
  AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  { ∑σ : perm.mod_sum_congr ιa ιb, dom_coprod.summand a b σ with
    toFun := fun v => («expr⇑ » (∑σ : perm.mod_sum_congr ιa ιb, dom_coprod.summand a b σ)) v,
    map_eq_zero_of_eq' :=
      fun v i j hv hij =>
        by 
          dsimp only 
          rw [MultilinearMap.sum_apply]
          exact
            Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
              (fun σ _ => dom_coprod.summand_add_swap_smul_eq_zero a b σ hv hij)
              (fun σ _ => mt$ dom_coprod.summand_eq_zero_of_smul_invariant a b σ hv hij) (fun σ _ => Finset.mem_univ _)
              fun σ _ => Equiv.Perm.ModSumCongr.swap_smul_involutive i j σ }

theorem dom_coprod_coe (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
  («expr↑ » (a.dom_coprod b) : MultilinearMap R' (fun _ => Mᵢ) _) =
    ∑σ : perm.mod_sum_congr ιa ιb, dom_coprod.summand a b σ :=
  MultilinearMap.ext$ fun _ => rfl

/-- A more bundled version of `alternating_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def dom_coprod' :
  AlternatingMap R' Mᵢ N₁ ιa ⊗[R'] AlternatingMap R' Mᵢ N₂ ιb →ₗ[R'] AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  TensorProduct.lift$
    by 
      refine' LinearMap.mk₂ R' dom_coprod (fun m₁ m₂ n => _) (fun c m n => _) (fun m n₁ n₂ => _) fun c m n => _ <;>
        ·
          ext 
          simp only [dom_coprod_apply, add_apply, smul_apply, ←Finset.sum_add_distrib, Finset.smul_sum,
            MultilinearMap.sum_apply, dom_coprod.summand]
          congr 
          ext σ 
          apply σ.induction_on' fun σ => _ 
          simp only [Quotientₓ.lift_on'_mk', coe_add, coe_smul, MultilinearMap.smul_apply,
            ←MultilinearMap.dom_coprod'_apply]
          simp only [TensorProduct.add_tmul, ←TensorProduct.smul_tmul', TensorProduct.tmul_add, TensorProduct.tmul_smul,
            LinearMap.map_add, LinearMap.map_smul]
          first |
            rw [←smul_add]|
            rw [smul_comm]
          congr

@[simp]
theorem dom_coprod'_apply (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
  dom_coprod' (a ⊗ₜ[R'] b) = dom_coprod a b :=
  by 
    simp only [dom_coprod', TensorProduct.lift.tmul, LinearMap.mk₂_apply]

end AlternatingMap

open Equiv

/-- A helper lemma for `multilinear_map.dom_coprod_alternization`. -/
theorem MultilinearMap.dom_coprod_alternization_coe (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁)
  (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
  MultilinearMap.domCoprod («expr↑ » a.alternatization) («expr↑ » b.alternatization) =
    ∑(σa : perm ιa)(σb : perm ιb),
      σa.sign • σb.sign • MultilinearMap.domCoprod (a.dom_dom_congr σa) (b.dom_dom_congr σb) :=
  by 
    simpRw [←MultilinearMap.dom_coprod'_apply, MultilinearMap.alternatization_coe]
    simpRw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, LinearMap.map_sum, ←TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, LinearMap.map_smul_of_tower]

open AlternatingMap

-- error in LinearAlgebra.Alternating: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Computing the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` is the same
as computing the `alternating_map.dom_coprod` of the `multilinear_map.alternatization`s.
-/
theorem multilinear_map.dom_coprod_alternization
(a : multilinear_map R' (λ _ : ιa, Mᵢ) N₁)
(b : multilinear_map R' (λ
  _ : ιb, Mᵢ) N₂) : «expr = »((multilinear_map.dom_coprod a b).alternatization, a.alternatization.dom_coprod b.alternatization) :=
begin
  apply [expr coe_multilinear_map_injective],
  rw ["[", expr dom_coprod_coe, ",", expr multilinear_map.alternatization_coe, ",", expr finset.sum_partition (quotient_group.left_rel (perm.sum_congr_hom ιa ιb).range), "]"] [],
  congr' [1] [],
  ext1 [] [ident σ],
  apply [expr σ.induction_on' (λ σ, _)],
  conv [] ["in", expr «expr = »(_, quotient.mk' _)] { change [expr «expr = »(quotient.mk' _, quotient.mk' _)],
    rw [expr quotient.eq'],
    rw ["[", expr quotient_group.left_rel, "]"],
    dsimp ["only"] ["[", expr setoid.r, "]"] [] },
  have [] [":", expr «expr = »(@finset.univ (perm «expr ⊕ »(ιa, ιb)) _, finset.univ.image (((«expr * »)) σ))] [":=", expr «expr $ »(finset.eq_univ_iff_forall.mpr, λ
    a, let ⟨a', ha'⟩ := mul_left_surjective σ a in
    finset.mem_image.mpr ⟨a', finset.mem_univ _, ha'⟩).symm],
  rw ["[", expr this, ",", expr finset.image_filter, "]"] [],
  simp [] [] ["only"] ["[", expr function.comp, ",", expr mul_inv_rev, ",", expr inv_mul_cancel_right, ",", expr subgroup.inv_mem_iff, "]"] [] [],
  simp [] [] ["only"] ["[", expr monoid_hom.mem_range, "]"] [] [],
  rw ["[", expr finset.filter_congr_decidable, ",", expr finset.univ_filter_exists (perm.sum_congr_hom ιa ιb), ",", expr finset.sum_image (λ
    (x _ y _)
    (h : «expr = »(_, _)), mul_right_injective _ h), ",", expr finset.sum_image (λ
    (x _ y _)
    (h : «expr = »(_, _)), perm.sum_congr_hom_injective h), "]"] [],
  dsimp ["only"] [] [] [],
  rw ["[", expr dom_coprod.summand_mk', ",", expr multilinear_map.dom_coprod_alternization_coe, ",", "<-", expr finset.sum_product', ",", expr finset.univ_product_univ, ",", "<-", expr multilinear_map.dom_dom_congr_equiv_apply, ",", expr add_equiv.map_sum, ",", expr finset.smul_sum, "]"] [],
  congr' [1] [],
  ext1 [] ["⟨", ident al, ",", ident ar, "⟩"],
  dsimp ["only"] [] [] [],
  rw ["[", "<-", expr add_equiv.coe_to_add_monoid_hom, ",", "<-", expr add_monoid_hom.coe_to_int_linear_map, ",", expr linear_map.map_smul_of_tower, ",", expr linear_map.map_smul_of_tower, ",", expr add_monoid_hom.coe_to_int_linear_map, ",", expr add_equiv.coe_to_add_monoid_hom, ",", expr multilinear_map.dom_dom_congr_equiv_apply, "]"] [],
  rw ["[", expr multilinear_map.dom_dom_congr_mul, ",", expr perm.sign_mul, ",", expr perm.sum_congr_hom_apply, ",", expr multilinear_map.dom_coprod_dom_dom_congr_sum_congr, ",", expr perm.sign_sum_congr, ",", expr mul_smul, ",", expr mul_smul, "]"] []
end

/-- Taking the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` of two
`alternating_map`s gives a scaled version of the `alternating_map.coprod` of those maps.
-/
theorem MultilinearMap.dom_coprod_alternization_eq (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
  (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗ N₂)).alternatization =
    ((Fintype.card ιa).factorial*(Fintype.card ιb).factorial) • a.dom_coprod b :=
  by 
    rw [MultilinearMap.dom_coprod_alternization, coe_alternatization, coe_alternatization, mul_smul, ←dom_coprod'_apply,
      ←dom_coprod'_apply, ←TensorProduct.smul_tmul', TensorProduct.tmul_smul, LinearMap.map_smul_of_tower dom_coprod',
      LinearMap.map_smul_of_tower dom_coprod']
    infer_instance 
    infer_instance

end Coprod

section Basis

open AlternatingMap

variable{ι₁ : Type _}[Fintype ι]

variable{R' : Type _}{N₁ N₂ : Type _}[CommSemiringₓ R'][AddCommMonoidₓ N₁][AddCommMonoidₓ N₂]

variable[Module R' N₁][Module R' N₂]

-- error in LinearAlgebra.Alternating: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Two alternating maps indexed by a `fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
theorem basis.ext_alternating
{f g : alternating_map R' N₁ N₂ ι}
(e : basis ι₁ R' N₁)
(h : ∀ v : ι → ι₁, function.injective v → «expr = »(f (λ i, e (v i)), g (λ i, e (v i)))) : «expr = »(f, g) :=
begin
  refine [expr alternating_map.coe_multilinear_map_injective «expr $ »(basis.ext_multilinear e, λ v, _)],
  by_cases [expr hi, ":", expr function.injective v],
  { exact [expr h v hi] },
  { have [] [":", expr «expr¬ »(function.injective (λ i, e (v i)))] [":=", expr hi.imp function.injective.of_comp],
    rw ["[", expr coe_multilinear_map, ",", expr coe_multilinear_map, ",", expr f.map_eq_zero_of_not_injective _ this, ",", expr g.map_eq_zero_of_not_injective _ this, "]"] [] }
end

end Basis

