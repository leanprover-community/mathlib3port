import Mathbin.Topology.UnitInterval
import Mathbin.Topology.Algebra.Ordered.ProjIcc
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.CompactOpen

/-!
# Homotopy between functions

In this file, we define a homotopy between two functions `f₀` and `f₁`. First we define 
`continuous_map.homotopy` between the two functions, with no restrictions on the intermediate 
maps. Then, as in the formalisation in HOL-Analysis, we define 
`continuous_map.homotopy_with f₀ f₁ P`, for homotopies between `f₀` and `f₁`, where the 
intermediate maps satisfy the predicate `P`. Finally, we define 
`continuous_map.homotopy_rel f₀ f₁ S`, for homotopies between `f₀` and `f₁` which are fixed 
on `S`.

## Definitions

* `continuous_map.homotopy f₀ f₁` is the type of homotopies between `f₀` and `f₁`.
* `continuous_map.homotopy_with f₀ f₁ P` is the type of homotopies between `f₀` and `f₁`, where
  the intermediate maps satisfy the predicate `P`.
* `continuous_map.homotopy_rel f₀ f₁ S` is the type of homotopies between `f₀` and `f₁` which 
  are fixed on `S`.

For each of the above, we have

* `refl f`, which is the constant homotopy from `f` to `f`.
* `symm F`, which reverses the homotopy `F`. For example, if `F : continuous_map.homotopy f₀ f₁`,
  then `F.symm : continuous_map.homotopy f₁ f₀`.
* `trans F G`, which concatenates the homotopies `F` and `G`. For example, if 
  `F : continuous_map.homotopy f₀ f₁` and `G : continuous_map.homotopy f₁ f₂`, then 
  `F.trans G : continuous_map.homotopy f₀ f₂`.

We also define the relations

* `continuous_map.homotopic f₀ f₁` is defined to be `nonempty (continuous_map.homotopy f₀ f₁)`
* `continuous_map.homotopic_with f₀ f₁ P` is defined to be 
  `nonempty (continuous_map.homotopy_with f₀ f₁ P)`
* `continuous_map.homotopic_rel f₀ f₁ P` is defined to be 
  `nonempty (continuous_map.homotopy_rel f₀ f₁ P)`

and for `continuous_map.homotopic` and `continuous_map.homotopic_rel`, we also define the 
`setoid` and `quotient` in `C(X, Y)` by these relations.

## References

- [HOL-Analysis formalisation](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html)
-/


noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open_locale UnitInterval

namespace ContinuousMap

/-- 
The type of homotopies between two functions.
-/
structure homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) where
  to_fun_zero : ∀ x, to_fun (0, x) = f₀ x
  to_fun_one : ∀ x, to_fun (1, x) = f₁ x

namespace Homotopy

section

variable {f₀ f₁ : C(X, Y)}

instance : CoeFun (homotopy f₀ f₁) fun _ => I × X → Y :=
  ⟨fun F => F.to_fun⟩

theorem coe_fn_injective : @Function.Injective (homotopy f₀ f₁) (I × X → Y) coeFn := by
  rintro ⟨⟨F, _⟩, _⟩ ⟨⟨G, _⟩, _⟩ h
  congr 2

@[ext]
theorem ext {F G : homotopy f₀ f₁} (h : ∀ x, F x = G x) : F = G :=
  coe_fn_injective $ funext h

/--  See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (F : homotopy f₀ f₁) : I × X → Y :=
  F

initialize_simps_projections Homotopy (to_continuous_map_to_fun → apply, -toContinuousMap)

@[continuity]
protected theorem Continuous (F : homotopy f₀ f₁) : Continuous F :=
  F.continuous_to_fun

@[simp]
theorem apply_zero (F : homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x :=
  F.to_fun_zero x

@[simp]
theorem apply_one (F : homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x :=
  F.to_fun_one x

@[simp]
theorem coe_to_continuous_map (F : homotopy f₀ f₁) : ⇑F.to_continuous_map = F :=
  rfl

/-- 
Currying a homotopy to a continuous function fron `I` to `C(X, Y)`.
-/
def curry (F : homotopy f₀ f₁) : C(I, C(X, Y)) :=
  F.to_continuous_map.curry

@[simp]
theorem curry_apply (F : homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) :=
  rfl

/-- 
Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : homotopy f₀ f₁) : C(ℝ, C(X, Y)) :=
  F.curry.Icc_extend zero_le_one

theorem extend_apply_of_le_zero (F : homotopy f₀ f₁) {t : ℝ} (ht : t ≤ 0) (x : X) : F.extend t x = f₀ x := by
  rw [← F.apply_zero]
  exact ContinuousMap.congr_fun (Set.Icc_extend_of_le_left (@zero_le_one ℝ _) F.curry ht) x

theorem extend_apply_of_one_le (F : homotopy f₀ f₁) {t : ℝ} (ht : 1 ≤ t) (x : X) : F.extend t x = f₁ x := by
  rw [← F.apply_one]
  exact ContinuousMap.congr_fun (Set.Icc_extend_of_right_le (@zero_le_one ℝ _) F.curry ht) x

@[simp]
theorem extend_apply_coe (F : homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (t, x) :=
  ContinuousMap.congr_fun (Set.Icc_extend_coe (@zero_le_one ℝ _) F.curry t) x

@[simp]
theorem extend_apply_of_mem_I (F : homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) (x : X) : F.extend t x = F (⟨t, ht⟩, x) :=
  ContinuousMap.congr_fun (Set.Icc_extend_of_mem (@zero_le_one ℝ _) F.curry ht) x

theorem congr_funₓ {F G : homotopy f₀ f₁} (h : F = G) (x : I × X) : F x = G x :=
  ContinuousMap.congr_fun (congr_argₓ _ h) x

theorem congr_argₓ (F : homotopy f₀ f₁) {x y : I × X} (h : x = y) : F x = F y :=
  F.to_continuous_map.congr_arg h

end

/-- 
Given a continuous function `f`, we can define a `homotopy f f` by `F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) : homotopy f f :=
  { toFun := fun x => f x.2, to_fun_zero := fun _ => rfl, to_fun_one := fun _ => rfl }

instance : Inhabited (homotopy (ContinuousMap.id : C(X, X)) ContinuousMap.id) :=
  ⟨homotopy.refl ContinuousMap.id⟩

/-- 
Given a `homotopy f₀ f₁`, we can define a `homotopy f₁ f₀` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : homotopy f₁ f₀ :=
  { toFun := fun x => F (σ x.1, x.2),
    to_fun_zero := by
      norm_num,
    to_fun_one := by
      norm_num }

@[simp]
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : F.symm.symm = F := by
  ext
  simp

/-- 
Given `homotopy f₀ f₁` and `homotopy f₁ f₂`, we can define a `homotopy f₀ f₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) : homotopy f₀ f₂ :=
  { toFun := fun x => if (x.1 : ℝ) ≤ 1 / 2 then F.extend (2*x.1) x.2 else G.extend ((2*x.1) - 1) x.2,
    continuous_to_fun := by
      refine'
        continuous_if_le (continuous_induced_dom.comp continuous_fst) continuous_const
          (F.continuous.comp
              (by
                continuity)).ContinuousOn
          (G.continuous.comp
              (by
                continuity)).ContinuousOn
          _
      rintro x hx
      norm_num [hx],
    to_fun_zero := fun x => by
      norm_num,
    to_fun_one := fun x => by
      norm_num }

theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then F (⟨2*x.1, (UnitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else G (⟨(2*x.1) - 1, UnitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, x.1.2.2⟩⟩, x.2) :=
  show ite _ _ _ = _ by
    split_ifs <;>
      ·
        rw [extend, ContinuousMap.coe_Icc_extend, Set.Icc_extend_of_mem]
        rfl

theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
  ext x
  simp only [symm_apply, trans_apply]
  split_ifs with h₁ h₂
  ·
    change (x.1 : ℝ) ≤ _ at h₂
    change (1 : ℝ) - x.1 ≤ _ at h₁
    have ht : (x.1 : ℝ) = 1 / 2 := by
      linarith
    norm_num [ht]
  ·
    congr 2
    apply Subtype.ext
    simp only [UnitInterval.coe_symm_eq, Subtype.coe_mk]
    linarith
  ·
    congr 2
    apply Subtype.ext
    simp only [UnitInterval.coe_symm_eq, Subtype.coe_mk]
    linarith
  ·
    change ¬(x.1 : ℝ) ≤ _ at h
    change ¬(1 : ℝ) - x.1 ≤ _ at h₁
    exfalso
    linarith

/-- 
Casting a `homotopy f₀ f₁` to a `homotopy g₀ g₁` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) : homotopy g₀ g₁ :=
  { toFun := F,
    to_fun_zero := by
      simp [← h₀],
    to_fun_one := by
      simp [← h₁] }

/-- 
If we have a `homotopy f₀ f₁` and a `homotopy g₀ g₁`, then we can compose them and get a
`homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
def hcomp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (F : homotopy f₀ f₁) (G : homotopy g₀ g₁) :
    homotopy (g₀.comp f₀) (g₁.comp f₁) :=
  { toFun := fun x => G (x.1, F x),
    to_fun_zero := by
      simp ,
    to_fun_one := by
      simp }

end Homotopy

/-- 
Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic if there exists a
`homotopy f₀ f₁`.
-/
def homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (homotopy f₀ f₁)

namespace Homotopic

@[refl]
theorem refl (f : C(X, Y)) : homotopic f f :=
  ⟨homotopy.refl f⟩

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : homotopic f g) : homotopic g f :=
  h.map homotopy.symm

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : homotopic f g) (h₁ : homotopic g h) : homotopic f h :=
  h₀.map2 homotopy.trans h₁

theorem hcomp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (h₀ : homotopic f₀ f₁) (h₁ : homotopic g₀ g₁) :
    homotopic (g₀.comp f₀) (g₁.comp f₁) :=
  h₀.map2 homotopy.hcomp h₁

theorem Equivalenceₓ : Equivalenceₓ (@homotopic X Y _ _) :=
  ⟨refl, symm, trans⟩

end Homotopic

/-- 
The type of homotopies between `f₀ f₁ : C(X, Y)`, where the intermediate maps satisfy the predicate
`P : C(X, Y) → Prop`
-/
structure homotopy_with (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends homotopy f₀ f₁ where
  prop' : ∀ t, P ⟨fun x => to_fun (t, x), Continuous.comp continuous_to_fun (continuous_const.prod_mk continuous_id')⟩

namespace HomotopyWith

section

variable {f₀ f₁ : C(X, Y)} {P : C(X, Y) → Prop}

instance : CoeFun (homotopy_with f₀ f₁ P) fun _ => I × X → Y :=
  ⟨fun F => F.to_fun⟩

theorem coe_fn_injective : @Function.Injective (homotopy_with f₀ f₁ P) (I × X → Y) coeFn := by
  rintro ⟨⟨⟨F, _⟩, _⟩, _⟩ ⟨⟨⟨G, _⟩, _⟩, _⟩ h
  congr 3

@[ext]
theorem ext {F G : homotopy_with f₀ f₁ P} (h : ∀ x, F x = G x) : F = G :=
  coe_fn_injective $ funext h

/--  See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (F : homotopy_with f₀ f₁ P) : I × X → Y :=
  F

initialize_simps_projections HomotopyWith (to_homotopy_to_continuous_map_to_fun → apply, -to_homotopy_to_continuous_map)

@[continuity]
protected theorem Continuous (F : homotopy_with f₀ f₁ P) : Continuous F :=
  F.continuous_to_fun

@[simp]
theorem apply_zero (F : homotopy_with f₀ f₁ P) (x : X) : F (0, x) = f₀ x :=
  F.to_fun_zero x

@[simp]
theorem apply_one (F : homotopy_with f₀ f₁ P) (x : X) : F (1, x) = f₁ x :=
  F.to_fun_one x

@[simp]
theorem coe_to_continuous_map (F : homotopy_with f₀ f₁ P) : ⇑F.to_continuous_map = F :=
  rfl

@[simp]
theorem coe_to_homotopy (F : homotopy_with f₀ f₁ P) : ⇑F.to_homotopy = F :=
  rfl

theorem prop (F : homotopy_with f₀ f₁ P) (t : I) : P (F.to_homotopy.curry t) :=
  F.prop' t

theorem extend_prop (F : homotopy_with f₀ f₁ P) (t : ℝ) : P (F.to_homotopy.extend t) := by
  by_cases' ht₀ : 0 ≤ t
  ·
    by_cases' ht₁ : t ≤ 1
    ·
      convert F.prop ⟨t, ht₀, ht₁⟩
      ext
      rw [F.to_homotopy.extend_apply_of_mem_I ⟨ht₀, ht₁⟩, F.to_homotopy.curry_apply]
    ·
      convert F.prop 1
      ext
      rw [F.to_homotopy.extend_apply_of_one_le (le_of_not_leₓ ht₁), F.to_homotopy.curry_apply, F.to_homotopy.apply_one]
  ·
    convert F.prop 0
    ext
    rw [F.to_homotopy.extend_apply_of_le_zero (le_of_not_leₓ ht₀), F.to_homotopy.curry_apply, F.to_homotopy.apply_zero]

end

variable {P : C(X, Y) → Prop}

/-- 
Given a continuous function `f`, and a proof `h : P f`, we can define a `homotopy_with f f P` by
`F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) (hf : P f) : homotopy_with f f P :=
  { homotopy.refl f with
    prop' := fun t => by
      convert hf
      cases f
      rfl }

instance : Inhabited (homotopy_with (ContinuousMap.id : C(X, X)) ContinuousMap.id fun f => True) :=
  ⟨homotopy_with.refl _ trivialₓ⟩

/-- 
Given a `homotopy_with f₀ f₁ P`, we can define a `homotopy_with f₁ f₀ P` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : homotopy_with f₀ f₁ P) : homotopy_with f₁ f₀ P :=
  { F.to_homotopy.symm with
    prop' := fun t => by
      simpa using F.prop (σ t) }

@[simp]
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : homotopy_with f₀ f₁ P) : F.symm.symm = F :=
  ext $ homotopy.congr_fun $ homotopy.symm_symm _

/-- 
Given `homotopy_with f₀ f₁ P` and `homotopy_with f₁ f₂ P`, we can define a `homotopy_with f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P) : homotopy_with f₀ f₂ P :=
  { F.to_homotopy.trans G.to_homotopy with
    prop' := fun t => by
      simp only [homotopy.trans]
      change P ⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩
      split_ifs
      ·
        exact F.extend_prop _
      ·
        exact G.extend_prop _ }

theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then F (⟨2*x.1, (UnitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else G (⟨(2*x.1) - 1, UnitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, x.1.2.2⟩⟩, x.2) :=
  homotopy.trans_apply _ _ _

theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ext $ homotopy.congr_fun $ homotopy.symm_trans _ _

/-- 
Casting a `homotopy_with f₀ f₁ P` to a `homotopy_with g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) : homotopy_with g₀ g₁ P :=
  { F.to_homotopy.cast h₀ h₁ with prop' := F.prop }

end HomotopyWith

/-- 
Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic with respect to the
predicate `P` if there exists a `homotopy_with f₀ f₁ P`.
-/
def homotopic_with (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) : Prop :=
  Nonempty (homotopy_with f₀ f₁ P)

namespace HomotopicWith

variable {P : C(X, Y) → Prop}

@[refl]
theorem refl (f : C(X, Y)) (hf : P f) : homotopic_with f f P :=
  ⟨homotopy_with.refl f hf⟩

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : homotopic_with f g P) : homotopic_with g f P :=
  ⟨h.some.symm⟩

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : homotopic_with f g P) (h₁ : homotopic_with g h P) : homotopic_with f h P :=
  ⟨h₀.some.trans h₁.some⟩

end HomotopicWith

/-- 
A `homotopy_rel f₀ f₁ S` is a homotopy between `f₀` and `f₁` which is fixed on the points in `S`.
-/
abbrev homotopy_rel (f₀ f₁ : C(X, Y)) (S : Set X) :=
  homotopy_with f₀ f₁ fun f => ∀, ∀ x ∈ S, ∀, f x = f₀ x ∧ f x = f₁ x

namespace HomotopyRel

section

variable {f₀ f₁ : C(X, Y)} {S : Set X}

theorem eq_fst (F : homotopy_rel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₀ x :=
  (F.prop t x hx).1

theorem eq_snd (F : homotopy_rel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₁ x :=
  (F.prop t x hx).2

theorem fst_eq_snd (F : homotopy_rel f₀ f₁ S) {x : X} (hx : x ∈ S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx

end

variable {f₀ f₁ f₂ : C(X, Y)} {S : Set X}

/-- 
Given a map `f : C(X, Y)` and a set `S`, we can define a `homotopy_rel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `homotopy_with.refl`, but with the proof
filled in.
-/
@[simps]
def refl (f : C(X, Y)) (S : Set X) : homotopy_rel f f S :=
  homotopy_with.refl f fun x hx => ⟨rfl, rfl⟩

/-- 
Given a `homotopy_rel f₀ f₁ S`, we can define a `homotopy_rel f₁ f₀ S` by reversing the homotopy.
-/
@[simps]
def symm (F : homotopy_rel f₀ f₁ S) : homotopy_rel f₁ f₀ S :=
  { homotopy_with.symm F with
    prop' := fun t x hx => by
      simp [F.eq_snd _ hx, F.fst_eq_snd hx] }

@[simp]
theorem symm_symm (F : homotopy_rel f₀ f₁ S) : F.symm.symm = F :=
  homotopy_with.symm_symm F

/-- 
Given `homotopy_rel f₀ f₁ S` and `homotopy_rel f₁ f₂ S`, we can define a `homotopy_rel f₀ f₂ S`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S) : homotopy_rel f₀ f₂ S :=
  { homotopy.trans F.to_homotopy G.to_homotopy with
    prop' := fun t => by
      intro x hx
      simp only [homotopy.trans]
      change (⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩ : C(X, Y)) _ = _ ∧ _ = _
      split_ifs
      ·
        simp [(homotopy_with.extend_prop F (2*t) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx]
      ·
        simp [(homotopy_with.extend_prop G ((2*t) - 1) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx] }

theorem trans_apply (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then F (⟨2*x.1, (UnitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else G (⟨(2*x.1) - 1, UnitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, x.1.2.2⟩⟩, x.2) :=
  homotopy.trans_apply _ _ _

theorem symm_trans (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S) : (F.trans G).symm = G.symm.trans F.symm :=
  homotopy_with.ext $ homotopy.congr_fun $ homotopy.symm_trans _ _

/-- 
Casting a `homotopy_rel f₀ f₁ S` to a `homotopy_rel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : homotopy_rel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) : homotopy_rel g₀ g₁ S :=
  { homotopy.cast F.to_homotopy h₀ h₁ with
    prop' := fun t x hx => by
      simpa [← h₀, ← h₁] using F.prop t x hx }

end HomotopyRel

/-- 
Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic relative to a set `S` if
there exists a `homotopy_rel f₀ f₁ S`.
-/
def homotopic_rel (f₀ f₁ : C(X, Y)) (S : Set X) : Prop :=
  Nonempty (homotopy_rel f₀ f₁ S)

namespace HomotopicRel

variable {S : Set X}

@[refl]
theorem refl (f : C(X, Y)) : homotopic_rel f f S :=
  ⟨homotopy_rel.refl f S⟩

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : homotopic_rel f g S) : homotopic_rel g f S :=
  h.map homotopy_rel.symm

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : homotopic_rel f g S) (h₁ : homotopic_rel g h S) : homotopic_rel f h S :=
  h₀.map2 homotopy_rel.trans h₁

theorem Equivalenceₓ : Equivalenceₓ fun f g : C(X, Y) => homotopic_rel f g S :=
  ⟨refl, symm, trans⟩

end HomotopicRel

end ContinuousMap

