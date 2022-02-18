import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: provide the dual result.
-/


noncomputable section

universe v u

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPullbacks C]

namespace HasEqualizersOfPullbacksAndBinaryProducts

/-- Define the equalizing object -/
@[reducible]
def construct_equalizer (F : walking_parallel_pair ⥤ C) : C :=
  pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left)) (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))

/-- Define the equalizing morphism -/
abbrev pullback_fst (F : walking_parallel_pair ⥤ C) : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero :=
  pullback.fst

theorem pullback_fst_eq_pullback_snd (F : walking_parallel_pair ⥤ C) : pullbackFst F = pullback.snd := by
  convert pullback.condition =≫ limits.prod.fst <;> simp

/-- Define the equalizing cone -/
@[reducible]
def equalizer_cone (F : walking_parallel_pair ⥤ C) : Cone F :=
  Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullback_fst_eq_pullback_snd]
        convert pullback.condition =≫ limits.prod.snd using 1 <;> simp ))

/-- Show the equalizing cone is a limit -/
def equalizer_cone_is_limit (F : walking_parallel_pair ⥤ C) : IsLimit (equalizerCone F) where
  lift := by
    intro c
    apply pullback.lift (c.π.app _) (c.π.app _)
    apply limit.hom_ext
    rintro (_ | _) <;> simp
  fac' := by
    rintro c (_ | _) <;> simp
  uniq' := by
    intro c _ J
    have J0 := J walking_parallel_pair.zero
    simp at J0
    apply pullback.hom_ext
    · rwa [limit.lift_π]
      
    · erw [limit.lift_π, ← J0, pullback_fst_eq_pullback_snd]
      

end HasEqualizersOfPullbacksAndBinaryProducts

open HasEqualizersOfPullbacksAndBinaryProducts

/-- Any category with pullbacks and binary products, has equalizers. -/
theorem has_equalizers_of_pullbacks_and_binary_products : HasEqualizers C :=
  { HasLimit := fun F => HasLimit.mk { Cone := equalizerCone F, IsLimit := equalizerConeIsLimit F } }

end CategoryTheory.Limits

