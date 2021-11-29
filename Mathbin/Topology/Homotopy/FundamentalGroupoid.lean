import Mathbin.CategoryTheory.Category.Groupoid 
import Mathbin.CategoryTheory.Groupoid 
import Mathbin.Topology.Category.Top.Basic 
import Mathbin.Topology.Homotopy.Path

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable theory

open_locale UnitInterval

namespace Path

namespace Homotopy

section 

/-- Auxilliary function for `refl_trans_symm` -/
def refl_trans_symm_aux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then (x.1*2)*x.2 else x.1*2 - 2*x.2

@[continuity]
theorem continuous_refl_trans_symm_aux : Continuous refl_trans_symm_aux :=
  by 
    refine' continuous_if_le _ _ (Continuous.continuous_on _) (Continuous.continuous_on _) _
    ·
      continuity
    ·
      continuity
    ·
      continuity
    ·
      continuity 
    intro x hx 
    normNum [hx, mul_assocₓ]

theorem refl_trans_symm_aux_mem_I (x : I × I) : refl_trans_symm_aux x ∈ I :=
  by 
    dsimp only [refl_trans_symm_aux]
    splitIfs
    ·
      split 
      ·
        apply mul_nonneg
        ·
          apply mul_nonneg
          ·
            unitInterval
          ·
            normNum
        ·
          unitInterval
      ·
        rw [mul_assocₓ]
        apply mul_le_one
        ·
          unitInterval
        ·
          apply mul_nonneg
          ·
            normNum
          ·
            unitInterval
        ·
          linarith
    ·
      split 
      ·
        apply mul_nonneg
        ·
          unitInterval 
        linarith [UnitInterval.nonneg x.2, UnitInterval.le_one x.2]
      ·
        apply mul_le_one
        ·
          unitInterval
        ·
          linarith [UnitInterval.nonneg x.2, UnitInterval.le_one x.2]
        ·
          linarith [UnitInterval.nonneg x.2, UnitInterval.le_one x.2]

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
def refl_trans_symm (p : Path x₀ x₁) : homotopy (Path.refl x₀) (p.trans p.symm) :=
  { toFun := fun x => p ⟨refl_trans_symm_aux x, refl_trans_symm_aux_mem_I x⟩,
    continuous_to_fun :=
      by 
        continuity,
    to_fun_zero :=
      by 
        normNum [refl_trans_symm_aux],
    to_fun_one :=
      fun x =>
        by 
          dsimp only [refl_trans_symm_aux, Path.coe_to_continuous_map, Path.trans]
          change _ = ite _ _ _ 
          splitIfs
          ·
            rw [Path.extend, Set.Icc_extend_of_mem]
            ·
              normNum
            ·
              rw [UnitInterval.mul_pos_mem_iff zero_lt_two]
              exact ⟨UnitInterval.nonneg x, h⟩
          ·
            rw [Path.symm, Path.extend, Set.Icc_extend_of_mem]
            ·
              congr 1 
              ext 
              normNum [sub_sub_assoc_swap]
            ·
              rw [UnitInterval.two_mul_sub_one_mem_iff]
              exact ⟨(not_leₓ.1 h).le, UnitInterval.le_one x⟩,
    prop' :=
      fun t x hx =>
        by 
          cases hx
          ·
            rw [hx]
            simp [refl_trans_symm_aux]
          ·
            rw [Set.mem_singleton_iff] at hx 
            rw [hx]
            normNum [refl_trans_symm_aux] }

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₁` to
  `p.symm.trans p`. -/
def refl_symm_trans (p : Path x₀ x₁) : homotopy (Path.refl x₁) (p.symm.trans p) :=
  (refl_trans_symm p.symm).cast rfl$ congr_argₓ _ Path.symm_symm

end 

section TransRefl

/-- Auxilliary function for `trans_refl_reparam` -/
def trans_refl_reparam_aux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then 2*t else 1

@[continuity]
theorem continuous_trans_refl_reparam_aux : Continuous trans_refl_reparam_aux :=
  by 
    refine' continuous_if_le _ _ (Continuous.continuous_on _) (Continuous.continuous_on _) _ <;> [continuity,
      continuity, continuity, continuity, skip]
    intro x hx 
    normNum [hx]

theorem trans_refl_reparam_aux_mem_I (t : I) : trans_refl_reparam_aux t ∈ I :=
  by 
    unfold trans_refl_reparam_aux 
    splitIfs <;> split  <;> linarith [UnitInterval.le_one t, UnitInterval.nonneg t]

theorem trans_refl_reparam_aux_zero : trans_refl_reparam_aux 0 = 0 :=
  by 
    normNum [trans_refl_reparam_aux]

theorem trans_refl_reparam_aux_one : trans_refl_reparam_aux 1 = 1 :=
  by 
    normNum [trans_refl_reparam_aux]

theorem trans_refl_reparam (p : Path x₀ x₁) :
  p.trans (Path.refl x₁) =
    p.reparam (fun t => ⟨trans_refl_reparam_aux t, trans_refl_reparam_aux_mem_I t⟩)
      (by 
        continuity)
      (Subtype.ext trans_refl_reparam_aux_zero) (Subtype.ext trans_refl_reparam_aux_one) :=
  by 
    ext 
    unfold trans_refl_reparam_aux 
    simp only [Path.trans_apply, not_leₓ, coe_to_fun, Function.comp_app]
    splitIfs
    ·
      rfl
    ·
      simp 

/--
For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (path.refl x₁)` to `p`.
-/
def trans_refl (p : Path x₀ x₁) : homotopy (p.trans (Path.refl x₁)) p :=
  ((homotopy.reparam p (fun t => ⟨trans_refl_reparam_aux t, trans_refl_reparam_aux_mem_I t⟩)
          (by 
            continuity)
          (Subtype.ext trans_refl_reparam_aux_zero) (Subtype.ext trans_refl_reparam_aux_one)).cast
      rfl (trans_refl_reparam p).symm).symm

/--
For any path `p` from `x₀` to `x₁`, we have a homotopy from `(path.refl x₀).trans p` to `p`.
-/
def refl_trans (p : Path x₀ x₁) : homotopy ((Path.refl x₀).trans p) p :=
  (trans_refl p.symm).symm₂.cast
    (by 
      simp )
    (by 
      simp )

end TransRefl

section Assoc

/-- Auxilliary function for `trans_assoc_reparam`. -/
def trans_assoc_reparam_aux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then 2*t else if (t : ℝ) ≤ 1 / 2 then t+1 / 4 else (1 / 2)*t+1

@[continuity]
theorem continuous_trans_assoc_reparam_aux : Continuous trans_assoc_reparam_aux :=
  by 
    refine'
          continuous_if_le _ _ (Continuous.continuous_on _)
            (continuous_if_le _ _ (Continuous.continuous_on _) (Continuous.continuous_on _) _).ContinuousOn _ <;>
        [continuity, continuity, continuity, continuity, continuity, continuity, continuity, skip, skip] <;>
      ·
        intro x hx 
        normNum [hx]

theorem trans_assoc_reparam_aux_mem_I (t : I) : trans_assoc_reparam_aux t ∈ I :=
  by 
    unfold trans_assoc_reparam_aux 
    splitIfs <;> split  <;> linarith [UnitInterval.le_one t, UnitInterval.nonneg t]

theorem trans_assoc_reparam_aux_zero : trans_assoc_reparam_aux 0 = 0 :=
  by 
    normNum [trans_assoc_reparam_aux]

theorem trans_assoc_reparam_aux_one : trans_assoc_reparam_aux 1 = 1 :=
  by 
    normNum [trans_assoc_reparam_aux]

-- error in Topology.Homotopy.FundamentalGroupoid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem trans_assoc_reparam
{x₀ x₁ x₂ x₃ : X}
(p : path x₀ x₁)
(q : path x₁ x₂)
(r : path x₂ x₃) : «expr = »((p.trans q).trans r, (p.trans (q.trans r)).reparam (λ
  t, ⟨trans_assoc_reparam_aux t, trans_assoc_reparam_aux_mem_I t⟩) (by continuity [] []) (subtype.ext trans_assoc_reparam_aux_zero) (subtype.ext trans_assoc_reparam_aux_one)) :=
begin
  ext [] [] [],
  simp [] [] ["only"] ["[", expr trans_assoc_reparam_aux, ",", expr path.trans_apply, ",", expr mul_inv_cancel_left₀, ",", expr not_le, ",", expr function.comp_app, ",", expr ne.def, ",", expr not_false_iff, ",", expr bit0_eq_zero, ",", expr one_ne_zero, ",", expr mul_ite, ",", expr subtype.coe_mk, ",", expr path.coe_to_fun, "]"] [] [],
  split_ifs [] ["with", ident h₁, ident h₂, ident h₃, ident h₄, ident h₅],
  { simp [] [] ["only"] ["[", expr one_div, ",", expr subtype.coe_mk, "]"] [] ["at", ident h₂],
    simp [] [] [] ["[", expr h₂, ",", expr h₃, "]"] [] [] },
  { exfalso,
    simp [] [] ["only"] ["[", expr subtype.coe_mk, "]"] [] ["at", ident h₂],
    linarith [] [] [] },
  { exfalso,
    simp [] [] ["only"] ["[", expr subtype.coe_mk, "]"] [] ["at", ident h₂],
    linarith [] [] [] },
  { have [ident h] [":", expr «expr¬ »(«expr ≤ »(«expr + »((x : exprℝ()), «expr / »(1, 4)), «expr / »(1, 2)))] [],
    by linarith [] [] [],
    have [ident h'] [":", expr «expr ≤ »(«expr - »(«expr * »(2, «expr + »((x : exprℝ()), «expr / »(1, 4))), 1), «expr / »(1, 2))] [],
    by linarith [] [] [],
    have [ident h''] [":", expr «expr = »(«expr - »(«expr * »(2, «expr * »(2, (x : exprℝ()))), 1), «expr * »(2, «expr - »(«expr * »(2, «expr + »(«expr↑ »(x), «expr / »(1, 4))), 1)))] [],
    by linarith [] [] [],
    simp [] [] ["only"] ["[", expr one_div, ",", expr subtype.coe_mk, "]"] [] ["at", ident h, ident h', ident h'', ident h₂],
    simp [] [] [] ["[", expr h₁, ",", expr h₂, ",", expr h₄, ",", expr h, ",", expr h', ",", expr h'', "]"] [] [] },
  { exfalso,
    linarith [] [] [] },
  { have [ident h] [":", expr «expr¬ »(«expr ≤ »(«expr * »((«expr / »(1, 2) : exprℝ()), «expr + »(x, 1)), «expr / »(1, 2)))] [],
    by linarith [] [] [],
    simp [] [] ["only"] ["[", expr one_div, "]"] [] ["at", ident h, ident h₁],
    simp [] [] [] ["[", expr h₁, ",", expr h₅, ",", expr h, "]"] [] [] }
end

/--
For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.trans r)`.
-/
def trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
  homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((homotopy.reparam (p.trans (q.trans r)) (fun t => ⟨trans_assoc_reparam_aux t, trans_assoc_reparam_aux_mem_I t⟩)
          (by 
            continuity)
          (Subtype.ext trans_assoc_reparam_aux_zero) (Subtype.ext trans_assoc_reparam_aux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm

end Assoc

end Homotopy

end Path

/--
The fundamental groupoid of a space `X` is defined to be a type synonym for `X`, and we subsequently
put a `category_theory.groupoid` structure on it.
-/
def FundamentalGroupoid (X : Type u) :=
  X

namespace FundamentalGroupoid

instance {X : Type u} [h : Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  h

attribute [local reducible] FundamentalGroupoid

attribute [local instance] Path.Homotopic.setoid

instance : CategoryTheory.Groupoid (FundamentalGroupoid X) :=
  { Hom := fun x y => Path.Homotopic.Quotient x y, id := fun x => «expr⟦ ⟧» (Path.refl x),
    comp := fun x y z => Quotientₓ.map₂ Path.trans fun p₀ : Path x y p₁ hp q₀ q₁ hq => Path.Homotopic.hcomp hp hq,
    id_comp' :=
      fun x y f =>
        Quotientₓ.induction_on f
          fun a =>
            show «expr⟦ ⟧» ((Path.refl x).trans a) = «expr⟦ ⟧» a from Quotientₓ.sound ⟨Path.Homotopy.reflTrans a⟩,
    comp_id' :=
      fun x y f =>
        Quotientₓ.induction_on f
          fun a =>
            show «expr⟦ ⟧» (a.trans (Path.refl y)) = «expr⟦ ⟧» a from Quotientₓ.sound ⟨Path.Homotopy.transRefl a⟩,
    assoc' :=
      fun w x y z f g h =>
        Quotientₓ.induction_on₃ f g h
          fun p q r =>
            show «expr⟦ ⟧» ((p.trans q).trans r) = «expr⟦ ⟧» (p.trans (q.trans r)) from
              Quotientₓ.sound ⟨Path.Homotopy.transAssoc p q r⟩,
    inv :=
      fun x y p =>
        Quotientₓ.lift (fun l : Path x y => «expr⟦ ⟧» l.symm)
          (by 
            rintro a b ⟨h⟩
            rw [Quotientₓ.eq]
            exact ⟨h.symm₂⟩)
          p,
    inv_comp' :=
      fun x y f =>
        Quotientₓ.induction_on f
          fun a =>
            show «expr⟦ ⟧» (a.symm.trans a) = «expr⟦ ⟧» (Path.refl y) from
              Quotientₓ.sound ⟨(Path.Homotopy.reflSymmTrans a).symm⟩,
    comp_inv' :=
      fun x y f =>
        Quotientₓ.induction_on f
          fun a =>
            show «expr⟦ ⟧» (a.trans a.symm) = «expr⟦ ⟧» (Path.refl x) from
              Quotientₓ.sound ⟨(Path.Homotopy.reflTransSymm a).symm⟩ }

theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) :
  p ≫ q = Quotientₓ.map₂ Path.trans (fun p₀ : Path x y p₁ hp q₀ q₁ hq => Path.Homotopic.hcomp hp hq) p q :=
  rfl

/--
The functor sending a topological space `X` to its fundamental groupoid.
-/
def fundamental_groupoid_functor : Top ⥤ CategoryTheory.Groupoidₓ :=
  { obj := fun X => { α := FundamentalGroupoid X },
    map :=
      fun X Y f =>
        { obj := f,
          map :=
            fun x y => Quotientₓ.map (fun q : Path x y => q.map f.continuous) fun p₀ p₁ h => Path.Homotopic.map h f,
          map_id' := fun X => rfl,
          map_comp' :=
            fun x y z p q =>
              Quotientₓ.induction_on₂ p q$
                fun a b =>
                  by 
                    simp [comp_eq] },
    map_id' :=
      by 
        intro X 
        change _ = (⟨_, _, _, _⟩ : FundamentalGroupoid X ⥤ FundamentalGroupoid X)
        congr 
        ext x y p 
        refine' Quotientₓ.induction_on p fun q => _ 
        rw [Quotientₓ.map_mk]
        convRHS => rw [←q.map_id]
        rfl,
    map_comp' :=
      by 
        intro X Y Z f g 
        congr 
        ext x y p 
        refine' Quotientₓ.induction_on p fun q => _ 
        simp only [Quotientₓ.map_mk, Path.map_map, Quotientₓ.eq]
        rfl }

end FundamentalGroupoid

