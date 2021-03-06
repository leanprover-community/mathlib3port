/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Extended norm

In this file we define a structure `enorm π V` representing an extended norm (i.e., a norm that can
take the value `β`) on a vector space `V` over a normed field `π`. We do not use `class` for
an `enorm` because the same space can have more than one extended norm. For example, the space of
measurable functions `f : Ξ± β β` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `emetric_space` structure on `V` corresponding to `e : enorm π V`;
* the subspace of vectors with finite norm, called `e.finite_subspace`;
* a `normed_space` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/


noncomputable section

attribute [local instance] Classical.propDecidable

open Ennreal

/-- Extended norm on a vector space. As in the case of normed spaces, we require only
`β₯c β’ xβ₯ β€ β₯cβ₯ * β₯xβ₯` in the definition, then prove an equality in `map_smul`. -/
structure Enorm (π : Type _) (V : Type _) [NormedField π] [AddCommGroupβ V] [Module π V] where
  toFun : V β ββ₯0β
  eq_zero' : β x, to_fun x = 0 β x = 0
  map_add_le' : β x y : V, to_fun (x + y) β€ to_fun x + to_fun y
  map_smul_le' : β (c : π) (x : V), to_fun (c β’ x) β€ β₯cβ₯β * to_fun x

namespace Enorm

variable {π : Type _} {V : Type _} [NormedField π] [AddCommGroupβ V] [Module π V] (e : Enorm π V)

instance : CoeFun (Enorm π V) fun _ => V β ββ₯0β :=
  β¨Enorm.toFunβ©

theorem coe_fn_injective : Function.Injective (coeFn : Enorm π V β V β ββ₯0β) := fun eβ eβ h => by
  cases eβ <;> cases eβ <;> congr <;> exact h

@[ext]
theorem ext {eβ eβ : Enorm π V} (h : β x, eβ x = eβ x) : eβ = eβ :=
  coe_fn_injective <| funext h

theorem ext_iff {eβ eβ : Enorm π V} : eβ = eβ β β x, eβ x = eβ x :=
  β¨fun h x => h βΈ rfl, extβ©

@[simp, norm_cast]
theorem coe_inj {eβ eβ : Enorm π V} : (eβ : V β ββ₯0β) = eβ β eβ = eβ :=
  coe_fn_injective.eq_iff

@[simp]
theorem map_smul (c : π) (x : V) : e (c β’ x) = β₯cβ₯β * e x :=
  le_antisymmβ (e.map_smul_le' c x) <| by
    by_cases' hc : c = 0
    Β· simp [β hc]
      
    calc (β₯cβ₯β : ββ₯0β) * e x = β₯cβ₯β * e (cβ»ΒΉ β’ c β’ x) := by
        rw [inv_smul_smulβ hc]_ β€ β₯cβ₯β * (β₯cβ»ΒΉβ₯β * e (c β’ x)) := _ _ = e (c β’ x) := _
    Β· exact Ennreal.mul_le_mul le_rfl (e.map_smul_le' _ _)
      
    Β· rw [β mul_assoc, nnnorm_inv, Ennreal.coe_inv, Ennreal.mul_inv_cancel _ Ennreal.coe_ne_top, one_mulβ] <;>
        simp [β hc]
      

@[simp]
theorem map_zero : e 0 = 0 := by
  rw [β zero_smul π (0 : V), e.map_smul]
  norm_num

@[simp]
theorem eq_zero_iff {x : V} : e x = 0 β x = 0 :=
  β¨e.eq_zero' x, fun h => h.symm βΈ e.map_zeroβ©

@[simp]
theorem map_neg (x : V) : e (-x) = e x :=
  calc
    e (-x) = β₯(-1 : π)β₯β * e x := by
      rw [β map_smul, neg_one_smul]
    _ = e x := by
      simp
    

theorem map_sub_rev (x y : V) : e (x - y) = e (y - x) := by
  rw [β neg_sub, e.map_neg]

theorem map_add_le (x y : V) : e (x + y) β€ e x + e y :=
  e.map_add_le' x y

theorem map_sub_le (x y : V) : e (x - y) β€ e x + e y :=
  calc
    e (x - y) = e (x + -y) := by
      rw [sub_eq_add_neg]
    _ β€ e x + e (-y) := e.map_add_le x (-y)
    _ = e x + e y := by
      rw [e.map_neg]
    

instance : PartialOrderβ (Enorm π V) where
  le := fun eβ eβ => β x, eβ x β€ eβ x
  le_refl := fun e x => le_rfl
  le_trans := fun eβ eβ eβ hββ hββ x => le_transβ (hββ x) (hββ x)
  le_antisymm := fun eβ eβ hββ hββ => ext fun x => le_antisymmβ (hββ x) (hββ x)

/-- The `enorm` sending each non-zero vector to infinity. -/
noncomputable instance : HasTop (Enorm π V) :=
  β¨{ toFun := fun x => if x = 0 then 0 else β€,
      eq_zero' := fun x => by
        split_ifs <;> simp [*],
      map_add_le' := fun x y => by
        split_ifs with hxy hx hy hy hx hy hy <;>
          try
            simp [*]
        simpa [β hx, β hy] using hxy,
      map_smul_le' := fun c x => by
        split_ifs with hcx hx hx <;> simp only [β smul_eq_zero, β not_or_distrib] at hcx
        Β· simp only [β mul_zero, β le_reflβ]
          
        Β· have : c = 0 := by
            tauto
          simp [β this]
          
        Β· tauto
          
        Β· simp [β hcx.1]
           }β©

noncomputable instance : Inhabited (Enorm π V) :=
  β¨β€β©

theorem top_map {x : V} (hx : x β  0) : (β€ : Enorm π V) x = β€ :=
  if_neg hx

noncomputable instance : OrderTop (Enorm π V) where
  top := β€
  le_top := fun e x =>
    if h : x = 0 then by
      simp [β h]
    else by
      simp [β top_map h]

noncomputable instance : SemilatticeSup (Enorm π V) :=
  { Enorm.partialOrder with le := (Β· β€ Β·), lt := (Β· < Β·),
    sup := fun eβ eβ =>
      { toFun := fun x => max (eβ x) (eβ x), eq_zero' := fun x h => eβ.eq_zero_iff.1 (Ennreal.max_eq_zero_iff.1 h).1,
        map_add_le' := fun x y =>
          max_leβ (le_transβ (eβ.map_add_le _ _) <| add_le_add (le_max_leftβ _ _) (le_max_leftβ _ _))
            (le_transβ (eβ.map_add_le _ _) <| add_le_add (le_max_rightβ _ _) (le_max_rightβ _ _)),
        map_smul_le' := fun c x =>
          le_of_eqβ <| by
            simp only [β map_smul, β Ennreal.mul_max] },
    le_sup_left := fun eβ eβ x => le_max_leftβ _ _, le_sup_right := fun eβ eβ x => le_max_rightβ _ _,
    sup_le := fun eβ eβ eβ hβ hβ x => max_leβ (hβ x) (hβ x) }

@[simp, norm_cast]
theorem coe_max (eβ eβ : Enorm π V) : β(eββeβ) = fun x => max (eβ x) (eβ x) :=
  rfl

@[norm_cast]
theorem max_map (eβ eβ : Enorm π V) (x : V) : (eββeβ) x = max (eβ x) (eβ x) :=
  rfl

/-- Structure of an `emetric_space` defined by an extended norm. -/
@[reducible]
def emetricSpace : EmetricSpace V where
  edist := fun x y => e (x - y)
  edist_self := fun x => by
    simp
  eq_of_edist_eq_zero := fun x y => by
    simp [β sub_eq_zero]
  edist_comm := e.map_sub_rev
  edist_triangle := fun x y z =>
    calc
      e (x - z) = e (x - y + (y - z)) := by
        rw [sub_add_sub_cancel]
      _ β€ e (x - y) + e (y - z) := e.map_add_le (x - y) (y - z)
      

/-- The subspace of vectors with finite enorm. -/
def finiteSubspace : Subspace π V where
  Carrier := { x | e x < β€ }
  zero_mem' := by
    simp
  add_mem' := fun x y hx hy => lt_of_le_of_ltβ (e.map_add_le x y) (Ennreal.add_lt_top.2 β¨hx, hyβ©)
  smul_mem' := fun c x (hx : _ < _) =>
    calc
      e (c β’ x) = β₯cβ₯β * e x := e.map_smul c x
      _ < β€ := Ennreal.mul_lt_top Ennreal.coe_ne_top hx.Ne
      

/-- Metric space structure on `e.finite_subspace`. We use `emetric_space.to_metric_space`
to ensure that this definition agrees with `e.emetric_space`. -/
instance : MetricSpace e.finiteSubspace := by
  let this := e.emetric_space
  refine' EmetricSpace.toMetricSpace fun x y => _
  change e (x - y) β  β€
  exact ne_top_of_le_ne_top (Ennreal.add_lt_top.2 β¨x.2, y.2β©).Ne (e.map_sub_le x y)

theorem finite_dist_eq (x y : e.finiteSubspace) : dist x y = (e (x - y)).toReal :=
  rfl

theorem finite_edist_eq (x y : e.finiteSubspace) : edist x y = e (x - y) :=
  rfl

/-- Normed group instance on `e.finite_subspace`. -/
instance : NormedGroup e.finiteSubspace :=
  { finiteSubspace.metricSpace e, Submodule.addCommGroup _ with norm := fun x => (e x).toReal,
    dist_eq := fun x y => rfl }

theorem finite_norm_eq (x : e.finiteSubspace) : β₯xβ₯ = (e x).toReal :=
  rfl

/-- Normed space instance on `e.finite_subspace`. -/
instance :
    NormedSpace π e.finiteSubspace where norm_smul_le := fun c x =>
    le_of_eqβ <| by
      simp [β finite_norm_eq, β Ennreal.to_real_mul]

end Enorm

