import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts 
import Mathbin.CategoryTheory.Limits.Shapes.Kernels 
import Mathbin.CategoryTheory.Limits.Shapes.NormalMono 
import Mathbin.CategoryTheory.Preadditive.Default

/-!
# Every non_preadditive_abelian category is preadditive

In mathlib, we define an abelian category as a preadditive category with a zero object,
kernels and cokernels, products and coproducts and in which every monomorphism and epimorphis is
normal.

While virtually every interesting abelian category has a natural preadditive structure (which is why
it is included in the definition), preadditivity is not actually needed: Every category that has
all of the other properties appearing in the definition of an abelian category admits a preadditive
structure. This is the construction we carry out in this file.

The proof proceeds in roughly five steps:
1. Prove some results (for example that all equalizers exist) that would be trivial if we already
   had the preadditive structure but are a bit of work without it.
2. Develop images and coimages to show that every monomorphism is the kernel of its cokernel.

The results of the first two steps are also useful for the "normal" development of abelian
categories, and will be used there.

3. For every object `A`, define a "subtraction" morphism `σ : A ⨯ A ⟶ A` and use it to define
   subtraction on morphisms as `f - g := prod.lift f g ≫ σ`.
4. Prove a small number of identities about this subtraction from the definition of `σ`.
5. From these identities, prove a large number of other identities that imply that defining
   `f + g := f - (0 - g)` indeed gives an abelian group structure on morphisms such that composition
   is bilinear.

The construction is non-trivial and it is quite remarkable that this abelian group structure can
be constructed purely from the existence of a few limits and colimits. What's even more impressive
is that all additive structures on a category are in some sense isomorphic, so for abelian
categories with a natural preadditive structure, this construction manages to "almost" reconstruct
this natural structure. However, we have not formalized this isomorphism.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

-/


noncomputable theory

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

section 

universe v u

variable(C : Type u)[category.{v} C]

/-- We call a category `non_preadditive_abelian` if it has a zero object, kernels, cokernels, binary
    products and coproducts, and every monomorphism and every epimorphism is normal. -/
class non_preadditive_abelian where 
  [HasZeroObject : has_zero_object C]
  [HasZeroMorphisms : has_zero_morphisms C]
  [HasKernels : has_kernels C]
  [HasCokernels : has_cokernels C]
  [HasFiniteProducts : has_finite_products C]
  [HasFiniteCoproducts : has_finite_coproducts C]
  NormalMono : ∀ {X Y : C} f : X ⟶ Y [mono f], normal_mono f 
  NormalEpi : ∀ {X Y : C} f : X ⟶ Y [epi f], normal_epi f

set_option default_priority 100

attribute [instance] non_preadditive_abelian.has_zero_object

attribute [instance] non_preadditive_abelian.has_zero_morphisms

attribute [instance] non_preadditive_abelian.has_kernels

attribute [instance] non_preadditive_abelian.has_cokernels

attribute [instance] non_preadditive_abelian.has_finite_products

attribute [instance] non_preadditive_abelian.has_finite_coproducts

end 

end CategoryTheory

open CategoryTheory

namespace CategoryTheory.NonPreadditiveAbelian

universe v u

variable{C : Type u}[category.{v} C]

section 

variable[non_preadditive_abelian C]

section Strong

attribute [local instance] non_preadditive_abelian.normal_epi

/-- In a `non_preadditive_abelian` category, every epimorphism is strong. -/
theorem strong_epi_of_epi {P Q : C} (f : P ⟶ Q) [epi f] : strong_epi f :=
  by 
    infer_instance

end Strong

section MonoEpiIso

variable{X Y : C}(f : X ⟶ Y)

attribute [local instance] strong_epi_of_epi

/-- In a `non_preadditive_abelian` category, a monomorphism which is also an epimorphism is an
    isomorphism. -/
theorem is_iso_of_mono_of_epi [mono f] [epi f] : is_iso f :=
  is_iso_of_mono_of_strong_epi _

end MonoEpiIso

/-- The pullback of two monomorphisms exists. -/
@[irreducible]
theorem pullback_of_mono {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [mono a] [mono b] : has_limit (cospan a b) :=
  let ⟨P, f, haf, i⟩ := non_preadditive_abelian.normal_mono a 
  let ⟨Q, g, hbg, i'⟩ := non_preadditive_abelian.normal_mono b 
  let ⟨a', ha'⟩ :=
    kernel_fork.is_limit.lift' i (kernel.ι (prod.lift f g))$
      calc kernel.ι (prod.lift f g) ≫ f = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ limits.prod.fst :=
        by 
          rw [prod.lift_fst]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ limits.prod.fst :=
        by 
          rw [kernel.condition_assoc]
        _ = 0 := zero_comp 
        
  let ⟨b', hb'⟩ :=
    kernel_fork.is_limit.lift' i' (kernel.ι (prod.lift f g))$
      calc kernel.ι (prod.lift f g) ≫ g = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ limits.prod.snd :=
        by 
          rw [prod.lift_snd]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ limits.prod.snd :=
        by 
          rw [kernel.condition_assoc]
        _ = 0 := zero_comp 
        
  has_limit.mk
    { Cone :=
        pullback_cone.mk a' b'$
          by 
            simp  at ha' hb' 
            rw [ha', hb'],
      IsLimit :=
        pullback_cone.is_limit.mk _
          (fun s =>
            kernel.lift (prod.lift f g) (pullback_cone.snd s ≫ b)$
              prod.hom_ext
                (calc ((pullback_cone.snd s ≫ b) ≫ prod.lift f g) ≫ limits.prod.fst = pullback_cone.snd s ≫ b ≫ f :=
                  by 
                    simp only [prod.lift_fst, category.assoc]
                  _ = pullback_cone.fst s ≫ a ≫ f :=
                  by 
                    rw [pullback_cone.condition_assoc]
                  _ = pullback_cone.fst s ≫ 0 :=
                  by 
                    rw [haf]
                  _ = 0 ≫ limits.prod.fst :=
                  by 
                    rw [comp_zero, zero_comp]
                  )
                (calc ((pullback_cone.snd s ≫ b) ≫ prod.lift f g) ≫ limits.prod.snd = pullback_cone.snd s ≫ b ≫ g :=
                  by 
                    simp only [prod.lift_snd, category.assoc]
                  _ = pullback_cone.snd s ≫ 0 :=
                  by 
                    rw [hbg]
                  _ = 0 ≫ limits.prod.snd :=
                  by 
                    rw [comp_zero, zero_comp]
                  ))
          (fun s =>
            (cancel_mono a).1$
              by 
                rw [kernel_fork.ι_of_ι] at ha' 
                simp [ha', pullback_cone.condition s])
          (fun s =>
            (cancel_mono b).1$
              by 
                rw [kernel_fork.ι_of_ι] at hb' 
                simp [hb'])
          fun s m h₁ h₂ =>
            (cancel_mono (kernel.ι (prod.lift f g))).1$
              calc m ≫ kernel.ι (prod.lift f g) = m ≫ a' ≫ a :=
                by 
                  congr 
                  exact ha'.symm 
                _ = pullback_cone.fst s ≫ a :=
                by 
                  rw [←category.assoc, h₁]
                _ = pullback_cone.snd s ≫ b := pullback_cone.condition s 
                _ = kernel.lift (prod.lift f g) (pullback_cone.snd s ≫ b) _ ≫ kernel.ι (prod.lift f g) :=
                by 
                  rw [kernel.lift_ι]
                 }

/-- The pushout of two epimorphisms exists. -/
@[irreducible]
theorem pushout_of_epi {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [epi a] [epi b] : has_colimit (span a b) :=
  let ⟨P, f, hfa, i⟩ := non_preadditive_abelian.normal_epi a 
  let ⟨Q, g, hgb, i'⟩ := non_preadditive_abelian.normal_epi b 
  let ⟨a', ha'⟩ :=
    cokernel_cofork.is_colimit.desc' i (cokernel.π (coprod.desc f g))$
      calc f ≫ cokernel.π (coprod.desc f g) = coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) :=
        by 
          rw [coprod.inl_desc_assoc]
        _ = coprod.inl ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) :=
        by 
          rw [cokernel.condition]
        _ = 0 := has_zero_morphisms.comp_zero _ _ 
        
  let ⟨b', hb'⟩ :=
    cokernel_cofork.is_colimit.desc' i' (cokernel.π (coprod.desc f g))$
      calc g ≫ cokernel.π (coprod.desc f g) = coprod.inr ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) :=
        by 
          rw [coprod.inr_desc_assoc]
        _ = coprod.inr ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) :=
        by 
          rw [cokernel.condition]
        _ = 0 := has_zero_morphisms.comp_zero _ _ 
        
  has_colimit.mk
    { Cocone :=
        pushout_cocone.mk a' b'$
          by 
            simp only [cofork.π_of_π] at ha' hb' 
            rw [ha', hb'],
      IsColimit :=
        pushout_cocone.is_colimit.mk _
          (fun s =>
            cokernel.desc (coprod.desc f g) (b ≫ pushout_cocone.inr s)$
              coprod.hom_ext
                (calc coprod.inl ≫ coprod.desc f g ≫ b ≫ pushout_cocone.inr s = f ≫ b ≫ pushout_cocone.inr s :=
                  by 
                    rw [coprod.inl_desc_assoc]
                  _ = f ≫ a ≫ pushout_cocone.inl s :=
                  by 
                    rw [pushout_cocone.condition]
                  _ = 0 ≫ pushout_cocone.inl s :=
                  by 
                    rw [reassoc_of hfa]
                  _ = coprod.inl ≫ 0 :=
                  by 
                    rw [comp_zero, zero_comp]
                  )
                (calc coprod.inr ≫ coprod.desc f g ≫ b ≫ pushout_cocone.inr s = g ≫ b ≫ pushout_cocone.inr s :=
                  by 
                    rw [coprod.inr_desc_assoc]
                  _ = 0 ≫ pushout_cocone.inr s :=
                  by 
                    rw [reassoc_of hgb]
                  _ = coprod.inr ≫ 0 :=
                  by 
                    rw [comp_zero, zero_comp]
                  ))
          (fun s =>
            (cancel_epi a).1$
              by 
                rw [cokernel_cofork.π_of_π] at ha' 
                simp [reassoc_of ha', pushout_cocone.condition s])
          (fun s =>
            (cancel_epi b).1$
              by 
                rw [cokernel_cofork.π_of_π] at hb' 
                simp [reassoc_of hb'])
          fun s m h₁ h₂ =>
            (cancel_epi (cokernel.π (coprod.desc f g))).1$
              calc cokernel.π (coprod.desc f g) ≫ m = (a ≫ a') ≫ m :=
                by 
                  congr 
                  exact ha'.symm 
                _ = a ≫ pushout_cocone.inl s :=
                by 
                  rw [category.assoc, h₁]
                _ = b ≫ pushout_cocone.inr s := pushout_cocone.condition s 
                _ = cokernel.π (coprod.desc f g) ≫ cokernel.desc (coprod.desc f g) (b ≫ pushout_cocone.inr s) _ :=
                by 
                  rw [cokernel.π_desc]
                 }

section 

attribute [local instance] pullback_of_mono

/-- The pullback of `(𝟙 X, f)` and `(𝟙 X, g)` -/
private abbrev P {X Y : C} (f g : X ⟶ Y) [mono (prod.lift (𝟙 X) f)] [mono (prod.lift (𝟙 X) g)] : C :=
  pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

/-- The equalizer of `f` and `g` exists. -/
@[irreducible]
theorem has_limit_parallel_pair {X Y : C} (f g : X ⟶ Y) : has_limit (parallel_pair f g) :=
  have huv : (pullback.fst : P f g ⟶ X) = pullback.snd :=
    calc (pullback.fst : P f g ⟶ X) = pullback.fst ≫ 𝟙 _ := Eq.symm$ category.comp_id _ 
      _ = pullback.fst ≫ prod.lift (𝟙 X) f ≫ limits.prod.fst :=
      by 
        rw [prod.lift_fst]
      _ = pullback.snd ≫ prod.lift (𝟙 X) g ≫ limits.prod.fst :=
      by 
        rw [pullback.condition_assoc]
      _ = pullback.snd :=
      by 
        rw [prod.lift_fst, category.comp_id]
      
  have hvu : (pullback.fst : P f g ⟶ X) ≫ f = pullback.snd ≫ g :=
    calc (pullback.fst : P f g ⟶ X) ≫ f = pullback.fst ≫ prod.lift (𝟙 X) f ≫ limits.prod.snd :=
      by 
        rw [prod.lift_snd]
      _ = pullback.snd ≫ prod.lift (𝟙 X) g ≫ limits.prod.snd :=
      by 
        rw [pullback.condition_assoc]
      _ = pullback.snd ≫ g :=
      by 
        rw [prod.lift_snd]
      
  have huu : (pullback.fst : P f g ⟶ X) ≫ f = pullback.fst ≫ g :=
    by 
      rw [hvu, ←huv]
  has_limit.mk
    { Cone := fork.of_ι pullback.fst huu,
      IsLimit :=
        fork.is_limit.mk _
          (fun s =>
            pullback.lift (fork.ι s) (fork.ι s)$
              prod.hom_ext
                (by 
                  simp only [prod.lift_fst, category.assoc])
                (by 
                  simp only [fork.app_zero_right, fork.app_zero_left, prod.lift_snd, category.assoc]))
          (fun s =>
            by 
              simp only [fork.ι_of_ι, pullback.lift_fst])
          fun s m h =>
            pullback.hom_ext
              (by 
                simpa only [pullback.lift_fst] using h walking_parallel_pair.zero)
              (by 
                simpa only [huv.symm, pullback.lift_fst] using h walking_parallel_pair.zero) }

end 

section 

attribute [local instance] pushout_of_epi

/-- The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`. -/
private abbrev Q {X Y : C} (f g : X ⟶ Y) [epi (coprod.desc (𝟙 Y) f)] [epi (coprod.desc (𝟙 Y) g)] : C :=
  pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

/-- The coequalizer of `f` and `g` exists. -/
@[irreducible]
theorem has_colimit_parallel_pair {X Y : C} (f g : X ⟶ Y) : has_colimit (parallel_pair f g) :=
  have huv : (pushout.inl : Y ⟶ Q f g) = pushout.inr :=
    calc (pushout.inl : Y ⟶ Q f g) = 𝟙 _ ≫ pushout.inl := Eq.symm$ category.id_comp _ 
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl :=
      by 
        rw [coprod.inl_desc]
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr :=
      by 
        simp only [category.assoc, pushout.condition]
      _ = pushout.inr :=
      by 
        rw [coprod.inl_desc, category.id_comp]
      
  have hvu : f ≫ (pushout.inl : Y ⟶ Q f g) = g ≫ pushout.inr :=
    calc f ≫ (pushout.inl : Y ⟶ Q f g) = (coprod.inr ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl :=
      by 
        rw [coprod.inr_desc]
      _ = (coprod.inr ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr :=
      by 
        simp only [category.assoc, pushout.condition]
      _ = g ≫ pushout.inr :=
      by 
        rw [coprod.inr_desc]
      
  have huu : f ≫ (pushout.inl : Y ⟶ Q f g) = g ≫ pushout.inl :=
    by 
      rw [hvu, huv]
  has_colimit.mk
    { Cocone := cofork.of_π pushout.inl huu,
      IsColimit :=
        cofork.is_colimit.mk _
          (fun s =>
            pushout.desc (cofork.π s) (cofork.π s)$
              coprod.hom_ext
                (by 
                  simp only [coprod.inl_desc_assoc])
                (by 
                  simp only [cofork.right_app_one, coprod.inr_desc_assoc, cofork.left_app_one]))
          (fun s =>
            by 
              simp only [pushout.inl_desc, cofork.π_of_π])
          fun s m h =>
            pushout.hom_ext
              (by 
                simpa only [pushout.inl_desc] using h walking_parallel_pair.one)
              (by 
                simpa only [huv.symm, pushout.inl_desc] using h walking_parallel_pair.one) }

end 

section 

attribute [local instance] has_limit_parallel_pair

/-- A `non_preadditive_abelian` category has all equalizers. -/
instance (priority := 100)has_equalizers : has_equalizers C :=
  has_equalizers_of_has_limit_parallel_pair _

end 

section 

attribute [local instance] has_colimit_parallel_pair

/-- A `non_preadditive_abelian` category has all coequalizers. -/
instance (priority := 100)has_coequalizers : has_coequalizers C :=
  has_coequalizers_of_has_colimit_parallel_pair _

end 

section 

/-- If a zero morphism is a kernel of `f`, then `f` is a monomorphism. -/
theorem mono_of_zero_kernel {X Y : C} (f : X ⟶ Y) (Z : C)
  (l :
    is_limit
      (kernel_fork.of_ι (0 : Z ⟶ X)
        (show 0 ≫ f = 0 by 
          simp ))) :
  mono f :=
  ⟨fun P u v huv =>
      by 
        obtain ⟨W, w, hw, hl⟩ := non_preadditive_abelian.normal_epi (coequalizer.π u v)
        obtain ⟨m, hm⟩ := coequalizer.desc' f huv 
        have hwf : w ≫ f = 0
        ·
          rw [←hm, reassoc_of hw, zero_comp]
        obtain ⟨n, hn⟩ := kernel_fork.is_limit.lift' l _ hwf 
        rw [fork.ι_of_ι, has_zero_morphisms.comp_zero] at hn 
        haveI  : is_iso (coequalizer.π u v)
        ·
          apply is_iso_colimit_cocone_parallel_pair_of_eq hn.symm hl 
        apply (cancel_mono (coequalizer.π u v)).1 
        exact coequalizer.condition _ _⟩

/-- If a zero morphism is a cokernel of `f`, then `f` is an epimorphism. -/
theorem epi_of_zero_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
  (l :
    is_colimit
      (cokernel_cofork.of_π (0 : Y ⟶ Z)
        (show f ≫ 0 = 0 by 
          simp ))) :
  epi f :=
  ⟨fun P u v huv =>
      by 
        obtain ⟨W, w, hw, hl⟩ := non_preadditive_abelian.normal_mono (equalizer.ι u v)
        obtain ⟨m, hm⟩ := equalizer.lift' f huv 
        have hwf : f ≫ w = 0
        ·
          rw [←hm, category.assoc, hw, comp_zero]
        obtain ⟨n, hn⟩ := cokernel_cofork.is_colimit.desc' l _ hwf 
        rw [cofork.π_of_π, zero_comp] at hn 
        haveI  : is_iso (equalizer.ι u v)
        ·
          apply is_iso_limit_cone_parallel_pair_of_eq hn.symm hl 
        apply (cancel_epi (equalizer.ι u v)).1 
        exact equalizer.condition _ _⟩

open_locale ZeroObject

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `0 : 0 ⟶ X` is a kernel of `f`. -/
def zero_kernel_of_cancel_zero {X Y : C} (f : X ⟶ Y) (hf : ∀ Z : C g : Z ⟶ X hgf : g ≫ f = 0, g = 0) :
  is_limit
    (kernel_fork.of_ι (0 : 0 ⟶ X)
      (show 0 ≫ f = 0 by 
        simp )) :=
  fork.is_limit.mk _ (fun s => 0)
    (fun s =>
      by 
        rw [hf _ _ (kernel_fork.condition s), zero_comp])
    fun s m h =>
      by 
        ext

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : Y ⟶ 0` is a cokernel of `f`. -/
def zero_cokernel_of_zero_cancel {X Y : C} (f : X ⟶ Y) (hf : ∀ Z : C g : Y ⟶ Z hgf : f ≫ g = 0, g = 0) :
  is_colimit
    (cokernel_cofork.of_π (0 : Y ⟶ 0)
      (show f ≫ 0 = 0 by 
        simp )) :=
  cofork.is_colimit.mk _ (fun s => 0)
    (fun s =>
      by 
        rw [hf _ _ (cokernel_cofork.condition s), comp_zero])
    fun s m h =>
      by 
        ext

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `f` is a monomorphism. -/
theorem mono_of_cancel_zero {X Y : C} (f : X ⟶ Y) (hf : ∀ Z : C g : Z ⟶ X hgf : g ≫ f = 0, g = 0) : mono f :=
  mono_of_zero_kernel f 0$ zero_kernel_of_cancel_zero f hf

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `g` is a monomorphism. -/
theorem epi_of_zero_cancel {X Y : C} (f : X ⟶ Y) (hf : ∀ Z : C g : Y ⟶ Z hgf : f ≫ g = 0, g = 0) : epi f :=
  epi_of_zero_cokernel f 0$ zero_cokernel_of_zero_cancel f hf

end 

section Factor

variable{P Q : C}(f : P ⟶ Q)

/-- The kernel of the cokernel of `f` is called the image of `f`. -/
protected abbrev image : C :=
  kernel (cokernel.π f)

/-- The inclusion of the image into the codomain. -/
protected abbrev image.ι : non_preadditive_abelian.image f ⟶ Q :=
  kernel.ι (cokernel.π f)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
protected abbrev factor_thru_image : P ⟶ non_preadditive_abelian.image f :=
  kernel.lift (cokernel.π f) f$ cokernel.condition f

/-- `f` factors through its image via the canonical morphism `p`. -/
@[simp, reassoc]
protected theorem image.fac : non_preadditive_abelian.factor_thru_image f ≫ image.ι f = f :=
  kernel.lift_ι _ _ _

/-- The map `p : P ⟶ image f` is an epimorphism -/
instance  : epi (non_preadditive_abelian.factor_thru_image f) :=
  let I := non_preadditive_abelian.image f 
  let p := non_preadditive_abelian.factor_thru_image f 
  let i := kernel.ι (cokernel.π f)
  epi_of_zero_cancel _$
    fun R g : I ⟶ R hpg : p ≫ g = 0 =>
      by 
        let u := kernel.ι g ≫ i 
        haveI  : mono u := mono_comp _ _ 
        haveI hu := non_preadditive_abelian.normal_mono u 
        let h := hu.g 
        obtain ⟨t, ht⟩ := kernel.lift' g p hpg 
        have fh : f ≫ h = 0
        calc f ≫ h = (p ≫ i) ≫ h := (image.fac f).symm ▸ rfl _ = ((t ≫ kernel.ι g) ≫ i) ≫ h := ht ▸ rfl _ = t ≫ u ≫ h :=
          by 
            simp only [category.assoc] <;> convLHS => congr skip rw [←category.assoc]_ = t ≫ 0 :=
          hu.w ▸ rfl _ = 0 := has_zero_morphisms.comp_zero _ _ 
        obtain ⟨l, hl⟩ := cokernel.desc' f h fh 
        have hih : i ≫ h = 0
        calc i ≫ h = i ≫ cokernel.π f ≫ l := hl ▸ rfl _ = 0 ≫ l :=
          by 
            rw [←category.assoc, kernel.condition]_ = 0 :=
          zero_comp 
        obtain ⟨s, hs⟩ := normal_mono.lift' u i hih 
        have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i
        ·
          rw [category.assoc, hs, category.id_comp]
        haveI  : epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs')
        exact zero_of_epi_comp _ (kernel.condition g)

instance mono_factor_thru_image [mono f] : mono (non_preadditive_abelian.factor_thru_image f) :=
  mono_of_mono_fac$ image.fac f

instance is_iso_factor_thru_image [mono f] : is_iso (non_preadditive_abelian.factor_thru_image f) :=
  is_iso_of_mono_of_epi _

/-- The cokernel of the kernel of `f` is called the coimage of `f`. -/
protected abbrev coimage : C :=
  cokernel (kernel.ι f)

/-- The projection onto the coimage. -/
protected abbrev coimage.π : P ⟶ non_preadditive_abelian.coimage f :=
  cokernel.π (kernel.ι f)

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
protected abbrev factor_thru_coimage : non_preadditive_abelian.coimage f ⟶ Q :=
  cokernel.desc (kernel.ι f) f$ kernel.condition f

/-- `f` factors through its coimage via the canonical morphism `p`. -/
protected theorem coimage.fac : coimage.π f ≫ non_preadditive_abelian.factor_thru_coimage f = f :=
  cokernel.π_desc _ _ _

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance  : mono (non_preadditive_abelian.factor_thru_coimage f) :=
  let I := non_preadditive_abelian.coimage f 
  let i := non_preadditive_abelian.factor_thru_coimage f 
  let p := cokernel.π (kernel.ι f)
  mono_of_cancel_zero _$
    fun R g : R ⟶ I hgi : g ≫ i = 0 =>
      by 
        let u := p ≫ cokernel.π g 
        haveI  : epi u := epi_comp _ _ 
        haveI hu := non_preadditive_abelian.normal_epi u 
        let h := hu.g 
        obtain ⟨t, ht⟩ := cokernel.desc' g i hgi 
        have hf : h ≫ f = 0
        calc h ≫ f = h ≫ p ≫ i := (coimage.fac f).symm ▸ rfl _ = h ≫ p ≫ cokernel.π g ≫ t := ht ▸ rfl _ = h ≫ u ≫ t :=
          by 
            simp only [category.assoc] <;> convLHS => congr skip rw [←category.assoc]_ = 0 ≫ t :=
          by 
            rw [←category.assoc, hu.w]_ = 0 :=
          zero_comp 
        obtain ⟨l, hl⟩ := kernel.lift' f h hf 
        have hhp : h ≫ p = 0
        calc h ≫ p = (l ≫ kernel.ι f) ≫ p := hl ▸ rfl _ = l ≫ 0 :=
          by 
            rw [category.assoc, cokernel.condition]_ = 0 :=
          comp_zero 
        obtain ⟨s, hs⟩ := normal_epi.desc' u p hhp 
        have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I
        ·
          rw [←category.assoc, hs, category.comp_id]
        haveI  : mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs')
        exact zero_of_comp_mono _ (cokernel.condition g)

instance epi_factor_thru_coimage [epi f] : epi (non_preadditive_abelian.factor_thru_coimage f) :=
  epi_of_epi_fac$ coimage.fac f

instance is_iso_factor_thru_coimage [epi f] : is_iso (non_preadditive_abelian.factor_thru_coimage f) :=
  is_iso_of_mono_of_epi _

end Factor

section CokernelOfKernel

variable{X Y : C}{f : X ⟶ Y}

/-- In a `non_preadditive_abelian` category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel [epi f] (s : fork f 0) (h : is_limit s) :
  is_colimit (cokernel_cofork.of_π f (kernel_fork.condition s)) :=
  is_cokernel.cokernel_iso _ _
    (cokernel.of_iso_comp _ _ (limits.is_limit.cone_point_unique_up_to_iso (limit.is_limit _) h)
      (cone_morphism.w (limits.is_limit.unique_up_to_iso (limit.is_limit _) h).hom _))
    (as_iso$ non_preadditive_abelian.factor_thru_coimage f) (coimage.fac f)

/-- In a `non_preadditive_abelian` category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def mono_is_kernel_of_cokernel [mono f] (s : cofork f 0) (h : is_colimit s) :
  is_limit (kernel_fork.of_ι f (cokernel_cofork.condition s)) :=
  is_kernel.iso_kernel _ _
    (kernel.of_comp_iso _ _ (limits.is_colimit.cocone_point_unique_up_to_iso h (colimit.is_colimit _))
      (cocone_morphism.w (limits.is_colimit.unique_up_to_iso h$ colimit.is_colimit _).hom _))
    (as_iso$ non_preadditive_abelian.factor_thru_image f) (image.fac f)

end CokernelOfKernel

section 

/-- The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` and the second map
    is the canonical projection into the cokernel. -/
abbrev r (A : C) : A ⟶ cokernel (diag A) :=
  prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)

instance mono_Δ {A : C} : mono (diag A) :=
  mono_of_mono_fac$ prod.lift_fst _ _

instance mono_r {A : C} : mono (r A) :=
  by 
    let hl : is_limit (kernel_fork.of_ι (diag A) (cokernel.condition (diag A)))
    ·
      exact mono_is_kernel_of_cokernel _ (colimit.is_colimit _)
    apply mono_of_cancel_zero 
    intro Z x hx 
    have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0
    ·
      rw [category.assoc, hx]
    obtain ⟨y, hy⟩ := kernel_fork.is_limit.lift' hl _ hxx 
    rw [kernel_fork.ι_of_ι] at hy 
    have hyy : y = 0
    ·
      erw [←category.comp_id y, ←limits.prod.lift_snd (𝟙 A) (𝟙 A), ←category.assoc, hy, category.assoc, prod.lift_snd,
        has_zero_morphisms.comp_zero]
    haveI  : mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
    apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
    rw [←hy, hyy, zero_comp, zero_comp]

instance epi_r {A : C} : epi (r A) :=
  by 
    have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ limits.prod.snd = 0 := prod.lift_snd _ _ 
    let hp1 : is_limit (kernel_fork.of_ι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp)
    ·
      refine' fork.is_limit.mk _ (fun s => fork.ι s ≫ limits.prod.fst) _ _
      ·
        intro s 
        ext <;> simp 
        erw [category.comp_id]
      ·
        intro s m h 
        haveI  : mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
        apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
        convert h walking_parallel_pair.zero 
        ext <;> simp 
    let hp2 : is_colimit (cokernel_cofork.of_π (limits.prod.snd : A ⨯ A ⟶ A) hlp)
    ·
      exact epi_is_cokernel_of_kernel _ hp1 
    apply epi_of_zero_cancel 
    intro Z z hz 
    have h : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ cokernel.π (diag A) ≫ z = 0
    ·
      rw [←category.assoc, hz]
    obtain ⟨t, ht⟩ := cokernel_cofork.is_colimit.desc' hp2 _ h 
    rw [cokernel_cofork.π_of_π] at ht 
    have htt : t = 0
    ·
      rw [←category.id_comp t]
      change 𝟙 A ≫ t = 0
      rw [←limits.prod.lift_snd (𝟙 A) (𝟙 A), category.assoc, ht, ←category.assoc, cokernel.condition, zero_comp]
    apply (cancel_epi (cokernel.π (diag A))).1
    rw [←ht, htt, comp_zero, comp_zero]

instance is_iso_r {A : C} : is_iso (r A) :=
  is_iso_of_mono_of_epi _

/-- The composite `A ⨯ A ⟶ cokernel (diag A) ⟶ A` given by the natural projection into the cokernel
    followed by the inverse of `r`. In the category of modules, using the normal kernels and
    cokernels, this map is equal to the map `(a, b) ↦ a - b`, hence the name `σ` for
    "subtraction". -/
abbrev σ {A : C} : A ⨯ A ⟶ A :=
  cokernel.π (diag A) ≫ inv (r A)

end 

@[simp, reassoc]
theorem diag_σ {X : C} : diag X ≫ σ = 0 :=
  by 
    rw [cokernel.condition_assoc, zero_comp]

@[simp, reassoc]
theorem lift_σ {X : C} : prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X :=
  by 
    rw [←category.assoc, is_iso.hom_inv_id]

@[reassoc]
theorem lift_map {X Y : C} (f : X ⟶ Y) : prod.lift (𝟙 X) 0 ≫ limits.prod.map f f = f ≫ prod.lift (𝟙 Y) 0 :=
  by 
    simp 

/-- σ is a cokernel of Δ X. -/
def is_colimit_σ {X : C} : is_colimit (cokernel_cofork.of_π σ diag_σ) :=
  cokernel.cokernel_iso _ σ (as_iso (r X)).symm
    (by 
      rw [iso.symm_hom, as_iso_inv])

/-- This is the key identity satisfied by `σ`. -/
theorem σ_comp {X Y : C} (f : X ⟶ Y) : σ ≫ f = limits.prod.map f f ≫ σ :=
  by 
    obtain ⟨g, hg⟩ :=
      cokernel_cofork.is_colimit.desc' is_colimit_σ (limits.prod.map f f ≫ σ)
        (by 
          simp )
    suffices hfg : f = g
    ·
      rw [←hg, cofork.π_of_π, hfg]
    calc f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ :=
      by 
        rw [lift_σ, category.comp_id]_ = prod.lift (𝟙 X) 0 ≫ limits.prod.map f f ≫ σ :=
      by 
        rw [lift_map_assoc]_ = prod.lift (𝟙 X) 0 ≫ σ ≫ g :=
      by 
        rw [←hg, cokernel_cofork.π_of_π]_ = g :=
      by 
        rw [←category.assoc, lift_σ, category.id_comp]

section 

/-- Subtraction of morphisms in a `non_preadditive_abelian` category. -/
def Sub {X Y : C} : Sub (X ⟶ Y) :=
  ⟨fun f g => prod.lift f g ≫ σ⟩

attribute [local instance] Sub

/-- Negation of morphisms in a `non_preadditive_abelian` category. -/
def Neg {X Y : C} : Neg (X ⟶ Y) :=
  ⟨fun f => 0 - f⟩

attribute [local instance] Neg

/-- Addition of morphisms in a `non_preadditive_abelian` category. -/
def Add {X Y : C} : Add (X ⟶ Y) :=
  ⟨fun f g => f - -g⟩

attribute [local instance] Add

theorem sub_def {X Y : C} (a b : X ⟶ Y) : a - b = prod.lift a b ≫ σ :=
  rfl

theorem add_def {X Y : C} (a b : X ⟶ Y) : (a+b) = a - -b :=
  rfl

theorem neg_def {X Y : C} (a : X ⟶ Y) : -a = 0 - a :=
  rfl

theorem sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a :=
  by 
    rw [sub_def]
    convLHS =>
      congr congr rw [←category.comp_id a]skip rw
        [show 0 = a ≫ (0 : Y ⟶ Y)by 
          simp ]
    rw [←prod.comp_lift, category.assoc, lift_σ, category.comp_id]

theorem sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0 :=
  by 
    rw [sub_def, ←category.comp_id a, ←prod.comp_lift, category.assoc, diag_σ, comp_zero]

theorem lift_sub_lift {X Y : C} (a b c d : X ⟶ Y) : prod.lift a b - prod.lift c d = prod.lift (a - c) (b - d) :=
  by 
    simp only [sub_def]
    ext
    ·
      rw [category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst]
    ·
      rw [category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd]

theorem sub_sub_sub {X Y : C} (a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d) :=
  by 
    rw [sub_def, ←lift_sub_lift, sub_def, category.assoc, σ_comp, prod.lift_map_assoc]
    rfl

theorem neg_sub {X Y : C} (a b : X ⟶ Y) : -a - b = -b - a :=
  by 
    convLHS => rw [neg_def, ←sub_zero b, sub_sub_sub, sub_zero, ←neg_def]

theorem neg_negₓ {X Y : C} (a : X ⟶ Y) : - -a = a :=
  by 
    rw [neg_def, neg_def]
    convLHS => congr rw [←sub_self a]
    rw [sub_sub_sub, sub_zero, sub_self, sub_zero]

theorem add_commₓ {X Y : C} (a b : X ⟶ Y) : (a+b) = b+a :=
  by 
    rw [add_def]
    convLHS => rw [←neg_negₓ a]
    rw [neg_def, neg_def, neg_def, sub_sub_sub]
    convLHS => congr skip rw [←neg_def, neg_sub]
    rw [sub_sub_sub, add_def, ←neg_def, neg_negₓ b, neg_def]

theorem add_neg {X Y : C} (a b : X ⟶ Y) : (a+-b) = a - b :=
  by 
    rw [add_def, neg_negₓ]

theorem add_neg_selfₓ {X Y : C} (a : X ⟶ Y) : (a+-a) = 0 :=
  by 
    rw [add_neg, sub_self]

theorem neg_add_selfₓ {X Y : C} (a : X ⟶ Y) : ((-a)+a) = 0 :=
  by 
    rw [add_commₓ, add_neg_selfₓ]

theorem neg_sub' {X Y : C} (a b : X ⟶ Y) : -(a - b) = (-a)+b :=
  by 
    rw [neg_def, neg_def]
    convLHS => rw [←sub_self (0 : X ⟶ Y)]
    rw [sub_sub_sub, add_def, neg_def]

theorem neg_add {X Y : C} (a b : X ⟶ Y) : (-a+b) = -a - b :=
  by 
    rw [add_def, neg_sub', add_neg]

theorem sub_add {X Y : C} (a b c : X ⟶ Y) : ((a - b)+c) = a - (b - c) :=
  by 
    rw [add_def, neg_def, sub_sub_sub, sub_zero]

theorem add_assocₓ {X Y : C} (a b c : X ⟶ Y) : ((a+b)+c) = a+b+c :=
  by 
    convLHS => congr rw [add_def]
    rw [sub_add, ←add_neg, neg_sub', neg_negₓ]

theorem add_zeroₓ {X Y : C} (a : X ⟶ Y) : (a+0) = a :=
  by 
    rw [add_def, neg_def, sub_self, sub_zero]

theorem comp_sub {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h :=
  by 
    rw [sub_def, ←category.assoc, prod.comp_lift, sub_def]

theorem sub_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h :=
  by 
    rw [sub_def, category.assoc, σ_comp, ←category.assoc, prod.lift_map, sub_def]

theorem comp_add (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z) : (f ≫ g+h) = (f ≫ g)+f ≫ h :=
  by 
    rw [add_def, comp_sub, neg_def, comp_sub, comp_zero, add_def, neg_def]

theorem add_comp (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z) : (f+g) ≫ h = (f ≫ h)+g ≫ h :=
  by 
    rw [add_def, sub_comp, neg_def, sub_comp, zero_comp, add_def, neg_def]

/-- Every `non_preadditive_abelian` category is preadditive. -/
def preadditive : preadditive C :=
  { homGroup :=
      fun X Y =>
        { add := ·+·, add_assoc := add_assocₓ, zero := 0, zero_add := neg_negₓ, add_zero := add_zeroₓ,
          neg := fun f => -f, add_left_neg := neg_add_selfₓ, add_comm := add_commₓ },
    add_comp' := add_comp, comp_add' := comp_add }

end 

end 

end CategoryTheory.NonPreadditiveAbelian

