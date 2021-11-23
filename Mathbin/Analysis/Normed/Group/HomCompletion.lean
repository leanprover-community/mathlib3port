import Mathbin.Analysis.Normed.Group.Hom 
import Mathbin.Analysis.Normed.Group.Completion

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : normed_group_hom G H`,
we build and study a normed group hom
`f.completion  : normed_group_hom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `normed_group_hom.completion`: see the discussion above.
* `normed_group.to_compl : normed_group_hom G (completion G)`: the canonical map from `G` to its
  completion, as a normed group hom
* `normed_group_hom.completion_to_compl`: the above diagram indeed commutes.
* `normed_group_hom.norm_completion`: `∥f.completion∥ = ∥f∥`
* `normed_group_hom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of the
  kernel of `f`.
* `normed_group_hom.ker_completion`: the kernel of `f.completion` is the closure of the image of the
  kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `normed_group_hom.extension` : if `H` is complete, the extension of `f : normed_group_hom G H`
  to a `normed_group_hom (completion G) H`.
-/


noncomputable theory

open Set NormedGroupHom UniformSpace

section Completion

variable{G : Type _}[SemiNormedGroup G]

variable{H : Type _}[SemiNormedGroup H]

variable{K : Type _}[SemiNormedGroup K]

/-- The normed group hom induced between completions. -/
def NormedGroupHom.completion (f : NormedGroupHom G H) : NormedGroupHom (completion G) (completion H) :=
  { f.to_add_monoid_hom.completion f.continuous with
    bound' :=
      by 
        use ∥f∥
        intro y 
        apply completion.induction_on y
        ·
          exact
            is_closed_le (continuous_norm.comp$ f.to_add_monoid_hom.continuous_completion f.continuous)
              (continuous_const.mul continuous_norm)
        ·
          intro x 
          change ∥f.to_add_monoid_hom.completion _ («expr↑ » x)∥ ≤ ∥f∥*∥«expr↑ » x∥
          rw [f.to_add_monoid_hom.completion_coe f.continuous]
          simp only [completion.norm_coe]
          exact f.le_op_norm x }

theorem NormedGroupHom.completion_def (f : NormedGroupHom G H) (x : completion G) :
  f.completion x = completion.map f x :=
  rfl

@[simp]
theorem NormedGroupHom.completion_coe_to_fun (f : NormedGroupHom G H) :
  (f.completion : completion G → completion H) = completion.map f :=
  by 
    ext x 
    exact NormedGroupHom.completion_def f x

@[simp]
theorem NormedGroupHom.completion_coe (f : NormedGroupHom G H) (g : G) : f.completion g = f g :=
  completion.map_coe f.uniform_continuous _

/-- Completion of normed group homs as a normed group hom. -/
@[simps]
def normedGroupHomCompletionHom : NormedGroupHom G H →+ NormedGroupHom (completion G) (completion H) :=
  { toFun := NormedGroupHom.completion,
    map_zero' :=
      by 
        apply to_add_monoid_hom_injective 
        exact AddMonoidHom.completion_zero,
    map_add' :=
      fun f g =>
        by 
          apply to_add_monoid_hom_injective 
          exact f.to_add_monoid_hom.completion_add g.to_add_monoid_hom f.continuous g.continuous }

@[simp]
theorem NormedGroupHom.completion_id : (NormedGroupHom.id G).Completion = NormedGroupHom.id (completion G) :=
  by 
    ext x 
    rw [NormedGroupHom.completion_def, NormedGroupHom.coe_id, completion.map_id]
    rfl

theorem NormedGroupHom.completion_comp (f : NormedGroupHom G H) (g : NormedGroupHom H K) :
  g.completion.comp f.completion = (g.comp f).Completion :=
  by 
    ext x 
    rw [NormedGroupHom.coe_comp, NormedGroupHom.completion_def, NormedGroupHom.completion_coe_to_fun,
      NormedGroupHom.completion_coe_to_fun,
      completion.map_comp (NormedGroupHom.uniform_continuous _) (NormedGroupHom.uniform_continuous _)]
    rfl

theorem NormedGroupHom.completion_neg (f : NormedGroupHom G H) : (-f).Completion = -f.completion :=
  normedGroupHomCompletionHom.map_neg f

theorem NormedGroupHom.completion_add (f g : NormedGroupHom G H) : (f+g).Completion = f.completion+g.completion :=
  normedGroupHomCompletionHom.map_add f g

theorem NormedGroupHom.completion_sub (f g : NormedGroupHom G H) : (f - g).Completion = f.completion - g.completion :=
  normedGroupHomCompletionHom.map_sub f g

@[simp]
theorem NormedGroupHom.zero_completion : (0 : NormedGroupHom G H).Completion = 0 :=
  normedGroupHomCompletionHom.map_zero

/-- The map from a normed group to its completion, as a normed group hom. -/
def NormedGroup.toCompl : NormedGroupHom G (completion G) :=
  { toFun := coeₓ, map_add' := completion.to_compl.map_add,
    bound' :=
      ⟨1,
        by 
          simp [le_reflₓ]⟩ }

open NormedGroup

theorem NormedGroup.norm_to_compl (x : G) : ∥to_compl x∥ = ∥x∥ :=
  completion.norm_coe x

theorem NormedGroup.dense_range_to_compl : DenseRange (to_compl : G → completion G) :=
  completion.dense_inducing_coe.dense

@[simp]
theorem NormedGroupHom.completion_to_compl (f : NormedGroupHom G H) : f.completion.comp to_compl = to_compl.comp f :=
  by 
    ext x 
    change f.completion x = _ 
    simpa

@[simp]
theorem NormedGroupHom.norm_completion (f : NormedGroupHom G H) : ∥f.completion∥ = ∥f∥ :=
  by 
    apply f.completion.op_norm_eq_of_bounds (norm_nonneg _)
    ·
      intro x 
      apply completion.induction_on x
      ·
        apply is_closed_le 
        continuity
      ·
        intro g 
        simp [f.le_op_norm g]
    ·
      intro N N_nonneg hN 
      apply f.op_norm_le_bound N_nonneg 
      intro x 
      simpa using hN x

theorem NormedGroupHom.ker_le_ker_completion (f : NormedGroupHom G H) :
  (to_compl.comp$ incl f.ker).range ≤ f.completion.ker :=
  by 
    intro a h 
    replace h : ∃ y : f.ker, to_compl (y : G) = a
    ·
      simpa using h 
    rcases h with ⟨⟨g, g_in : g ∈ f.ker⟩, rfl⟩
    rw [f.mem_ker] at g_in 
    change f.completion (g : completion G) = 0
    simp [NormedGroupHom.mem_ker, f.completion_coe g, g_in, completion.coe_zero]

-- error in Analysis.Normed.Group.HomCompletion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normed_group_hom.ker_completion
{f : normed_group_hom G H}
{C : exprℝ()}
(h : f.surjective_on_with f.range C) : «expr = »((f.completion.ker : «expr $ »(set, completion G)), closure «expr $ »(to_compl.comp, incl f.ker).range) :=
begin
  rcases [expr h.exists_pos, "with", "⟨", ident C', ",", ident C'_pos, ",", ident hC', "⟩"],
  apply [expr le_antisymm],
  { intros [ident hatg, ident hatg_in],
    rw [expr semi_normed_group.mem_closure_iff] [],
    intros [ident ε, ident ε_pos],
    have [ident hCf] [":", expr «expr ≤ »(0, «expr * »(C', «expr∥ ∥»(f)))] [":=", expr (zero_le_mul_left C'_pos).mpr (norm_nonneg f)],
    have [ident ineq] [":", expr «expr < »(0, «expr + »(1, «expr * »(C', «expr∥ ∥»(f))))] [],
    by linarith [] [] [],
    set [] [ident δ] [] [":="] [expr «expr / »(ε, «expr + »(1, «expr * »(C', «expr∥ ∥»(f))))] [],
    have [ident δ_pos] [":", expr «expr > »(δ, 0)] [],
    from [expr div_pos ε_pos ineq],
    obtain ["⟨", "_", ",", "⟨", ident g, ":", expr G, ",", ident rfl, "⟩", ",", ident hg, ":", expr «expr < »(«expr∥ ∥»(«expr - »(hatg, g)), δ), "⟩", ":=", expr semi_normed_group.mem_closure_iff.mp (completion.dense_inducing_coe.dense hatg) δ δ_pos],
    obtain ["⟨", ident g', ":", expr G, ",", ident hgg', ":", expr «expr = »(f g', f g), ",", ident hfg, ":", expr «expr ≤ »(«expr∥ ∥»(g'), «expr * »(C', «expr∥ ∥»(f g))), "⟩", ":=", expr hC' (f g) (mem_range_self g)],
    have [ident mem_ker] [":", expr «expr ∈ »(«expr - »(g, g'), f.ker)] [],
    by rw ["[", expr f.mem_ker, ",", expr f.map_sub, ",", expr sub_eq_zero.mpr hgg'.symm, "]"] [],
    have [] [":", expr «expr ≤ »(«expr∥ ∥»(f g), «expr * »(«expr∥ ∥»(f), «expr∥ ∥»(«expr - »(hatg, g))))] [],
    calc
      «expr = »(«expr∥ ∥»(f g), «expr∥ ∥»(f.completion g)) : by rw ["[", expr f.completion_coe, ",", expr completion.norm_coe, "]"] []
      «expr = »(..., «expr∥ ∥»(«expr - »(f.completion g, 0))) : by rw ["[", expr sub_zero _, "]"] []
      «expr = »(..., «expr∥ ∥»(«expr - »(f.completion g, f.completion hatg))) : by rw ["[", expr (f.completion.mem_ker _).mp hatg_in, "]"] []
      «expr = »(..., «expr∥ ∥»(f.completion «expr - »(g, hatg))) : by rw ["[", expr f.completion.map_sub, "]"] []
      «expr ≤ »(..., «expr * »(«expr∥ ∥»(f.completion), «expr∥ ∥»(«expr - »((g : completion G), hatg)))) : f.completion.le_op_norm _
      «expr = »(..., «expr * »(«expr∥ ∥»(f), «expr∥ ∥»(«expr - »(hatg, g)))) : by rw ["[", expr norm_sub_rev, ",", expr f.norm_completion, "]"] [],
    have [] [":", expr «expr ≤ »(«expr∥ ∥»((g' : completion G)), «expr * »(«expr * »(C', «expr∥ ∥»(f)), «expr∥ ∥»(«expr - »(hatg, g))))] [],
    calc
      «expr = »(«expr∥ ∥»((g' : completion G)), «expr∥ ∥»(g')) : completion.norm_coe _
      «expr ≤ »(..., «expr * »(C', «expr∥ ∥»(f g))) : hfg
      «expr ≤ »(..., «expr * »(«expr * »(C', «expr∥ ∥»(f)), «expr∥ ∥»(«expr - »(hatg, g)))) : by { rw [expr mul_assoc] [],
        exact [expr (mul_le_mul_left C'_pos).mpr this] },
    refine [expr ⟨«expr - »(g, g'), _, _⟩],
    { norm_cast [],
      rw [expr normed_group_hom.comp_range] [],
      apply [expr add_subgroup.mem_map_of_mem],
      simp [] [] ["only"] ["[", expr incl_range, ",", expr mem_ker, "]"] [] [] },
    { calc
        «expr = »(«expr∥ ∥»(«expr - »(hatg, «expr - »(g, g'))), «expr∥ ∥»(«expr + »(«expr - »(hatg, g), g'))) : by abel [] [] []
        «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr - »(hatg, g)), «expr∥ ∥»((g' : completion G)))) : norm_add_le _ _
        «expr < »(..., «expr + »(δ, «expr * »(«expr * »(C', «expr∥ ∥»(f)), «expr∥ ∥»(«expr - »(hatg, g))))) : by linarith [] [] []
        «expr ≤ »(..., «expr + »(δ, «expr * »(«expr * »(C', «expr∥ ∥»(f)), δ))) : add_le_add_left (mul_le_mul_of_nonneg_left hg.le hCf) δ
        «expr = »(..., «expr * »(«expr + »(1, «expr * »(C', «expr∥ ∥»(f))), δ)) : by ring []
        «expr = »(..., ε) : mul_div_cancel' _ ineq.ne.symm } },
  { rw ["<-", expr f.completion.is_closed_ker.closure_eq] [],
    exact [expr closure_mono f.ker_le_ker_completion] }
end

end Completion

section Extension

variable{G : Type _}[SemiNormedGroup G]

variable{H : Type _}[SemiNormedGroup H][SeparatedSpace H][CompleteSpace H]

/-- If `H` is complete, the extension of `f : normed_group_hom G H` to a
`normed_group_hom (completion G) H`. -/
def NormedGroupHom.extension (f : NormedGroupHom G H) : NormedGroupHom (completion G) H :=
  { f.to_add_monoid_hom.extension f.continuous with
    bound' :=
      by 
        refine' ⟨∥f∥, fun v => completion.induction_on v (is_closed_le _ _) fun a => _⟩
        ·
          exact Continuous.comp continuous_norm completion.continuous_extension
        ·
          exact Continuous.mul continuous_const continuous_norm
        ·
          rw [completion.norm_coe, AddMonoidHom.to_fun_eq_coe, AddMonoidHom.extension_coe]
          exact le_op_norm f a }

theorem NormedGroupHom.extension_def (f : NormedGroupHom G H) (v : G) : f.extension v = completion.extension f v :=
  rfl

@[simp]
theorem NormedGroupHom.extension_coe (f : NormedGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.continuous _

theorem NormedGroupHom.extension_coe_to_fun (f : NormedGroupHom G H) :
  (f.extension : completion G → H) = completion.extension f :=
  rfl

theorem NormedGroupHom.extension_unique (f : NormedGroupHom G H) {g : NormedGroupHom (completion G) H}
  (hg : ∀ v, f v = g v) : f.extension = g :=
  by 
    ext v 
    rw [NormedGroupHom.extension_coe_to_fun,
      completion.extension_unique f.uniform_continuous g.uniform_continuous fun a => hg a]

end Extension

