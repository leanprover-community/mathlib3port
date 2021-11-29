import Mathbin.CategoryTheory.Limits.Shapes.Equalizers 
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts 
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: provide the dual result.
-/


noncomputable theory

universe v u

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [category.{v} C] [has_binary_products C] [has_pullbacks C]

namespace HasEqualizersOfPullbacksAndBinaryProducts

/-- Define the equalizing object -/
@[reducible]
def construct_equalizer (F : walking_parallel_pair ⥤ C) : C :=
  pullback (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.left))
    (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.right))

/-- Define the equalizing morphism -/
abbrev pullback_fst (F : walking_parallel_pair ⥤ C) : construct_equalizer F ⟶ F.obj walking_parallel_pair.zero :=
  pullback.fst

theorem pullback_fst_eq_pullback_snd (F : walking_parallel_pair ⥤ C) : pullback_fst F = pullback.snd :=
  by 
    convert pullback.condition =≫ limits.prod.fst <;> simp 

/-- Define the equalizing cone -/
@[reducible]
def equalizer_cone (F : walking_parallel_pair ⥤ C) : cone F :=
  cone.of_fork
    (fork.of_ι (pullback_fst F)
      (by 
        convRHS => rw [pullback_fst_eq_pullback_snd]
        convert pullback.condition =≫ limits.prod.snd using 1 <;> simp ))

-- error in CategoryTheory.Limits.Constructions.Equalizers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Show the equalizing cone is a limit -/
def equalizer_cone_is_limit (F : «expr ⥤ »(walking_parallel_pair, C)) : is_limit (equalizer_cone F) :=
{ lift := begin
    intro [ident c],
    apply [expr pullback.lift (c.π.app _) (c.π.app _)],
    apply [expr limit.hom_ext],
    rintro ["(", "_", "|", "_", ")"]; simp [] [] [] [] [] []
  end,
  fac' := by rintros [ident c, "(", "_", "|", "_", ")"]; simp [] [] [] [] [] [],
  uniq' := begin
    intros [ident c, "_", ident J],
    have [ident J0] [] [":=", expr J walking_parallel_pair.zero],
    simp [] [] [] [] [] ["at", ident J0],
    apply [expr pullback.hom_ext],
    { rwa [expr limit.lift_π] [] },
    { erw ["[", expr limit.lift_π, ",", "<-", expr J0, ",", expr pullback_fst_eq_pullback_snd, "]"] [] }
  end }

end HasEqualizersOfPullbacksAndBinaryProducts

open HasEqualizersOfPullbacksAndBinaryProducts

/-- Any category with pullbacks and binary products, has equalizers. -/
theorem has_equalizers_of_pullbacks_and_binary_products : has_equalizers C :=
  { HasLimit := fun F => has_limit.mk { Cone := equalizer_cone F, IsLimit := equalizer_cone_is_limit F } }

end CategoryTheory.Limits

