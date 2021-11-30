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

variable (C : Type u) [category.{v} C]

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

variable {C : Type u} [category.{v} C]

section 

variable [non_preadditive_abelian C]

section Strong

attribute [local instance] non_preadditive_abelian.normal_epi

/-- In a `non_preadditive_abelian` category, every epimorphism is strong. -/
theorem strong_epi_of_epi {P Q : C} (f : P ⟶ Q) [epi f] : strong_epi f :=
  by 
    infer_instance

end Strong

section MonoEpiIso

variable {X Y : C} (f : X ⟶ Y)

attribute [local instance] strong_epi_of_epi

/-- In a `non_preadditive_abelian` category, a monomorphism which is also an epimorphism is an
    isomorphism. -/
theorem is_iso_of_mono_of_epi [mono f] [epi f] : is_iso f :=
  is_iso_of_mono_of_strong_epi _

end MonoEpiIso

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:927:38: unsupported irreducible non-definition
/-- The pullback of two monomorphisms exists. -/
@[irreducible]
theorem pullback_of_mono
{X Y Z : C}
(a : «expr ⟶ »(X, Z))
(b : «expr ⟶ »(Y, Z))
[mono a]
[mono b] : has_limit (cospan a b) :=
let ⟨P, f, haf, i⟩ := non_preadditive_abelian.normal_mono a in
let ⟨Q, g, hbg, i'⟩ := non_preadditive_abelian.normal_mono b in
let ⟨a', ha'⟩ := «expr $ »(kernel_fork.is_limit.lift' i (kernel.ι (prod.lift f g)), calc
       «expr = »(«expr ≫ »(kernel.ι (prod.lift f g), f), «expr ≫ »(kernel.ι (prod.lift f g), «expr ≫ »(prod.lift f g, limits.prod.fst))) : by rw [expr prod.lift_fst] []
       «expr = »(..., «expr ≫ »((0 : «expr ⟶ »(kernel (prod.lift f g), «expr ⨯ »(P, Q))), limits.prod.fst)) : by rw [expr kernel.condition_assoc] []
       «expr = »(..., 0) : zero_comp) in
let ⟨b', hb'⟩ := «expr $ »(kernel_fork.is_limit.lift' i' (kernel.ι (prod.lift f g)), calc
       «expr = »(«expr ≫ »(kernel.ι (prod.lift f g), g), «expr ≫ »(kernel.ι (prod.lift f g), «expr ≫ »(prod.lift f g, limits.prod.snd))) : by rw [expr prod.lift_snd] []
       «expr = »(..., «expr ≫ »((0 : «expr ⟶ »(kernel (prod.lift f g), «expr ⨯ »(P, Q))), limits.prod.snd)) : by rw [expr kernel.condition_assoc] []
       «expr = »(..., 0) : zero_comp) in
has_limit.mk { cone := «expr $ »(pullback_cone.mk a' b', by { simp [] [] [] [] [] ["at", ident ha', ident hb'],
     rw ["[", expr ha', ",", expr hb', "]"] [] }),
  is_limit := pullback_cone.is_limit.mk _ (λ
   s, «expr $ »(kernel.lift (prod.lift f g) «expr ≫ »(pullback_cone.snd s, b), prod.hom_ext (calc
       «expr = »(«expr ≫ »(«expr ≫ »(«expr ≫ »(pullback_cone.snd s, b), prod.lift f g), limits.prod.fst), «expr ≫ »(pullback_cone.snd s, «expr ≫ »(b, f))) : by simp [] [] ["only"] ["[", expr prod.lift_fst, ",", expr category.assoc, "]"] [] []
       «expr = »(..., «expr ≫ »(pullback_cone.fst s, «expr ≫ »(a, f))) : by rw [expr pullback_cone.condition_assoc] []
       «expr = »(..., «expr ≫ »(pullback_cone.fst s, 0)) : by rw [expr haf] []
       «expr = »(..., «expr ≫ »(0, limits.prod.fst)) : by rw ["[", expr comp_zero, ",", expr zero_comp, "]"] []) (calc
       «expr = »(«expr ≫ »(«expr ≫ »(«expr ≫ »(pullback_cone.snd s, b), prod.lift f g), limits.prod.snd), «expr ≫ »(pullback_cone.snd s, «expr ≫ »(b, g))) : by simp [] [] ["only"] ["[", expr prod.lift_snd, ",", expr category.assoc, "]"] [] []
       «expr = »(..., «expr ≫ »(pullback_cone.snd s, 0)) : by rw [expr hbg] []
       «expr = »(..., «expr ≫ »(0, limits.prod.snd)) : by rw ["[", expr comp_zero, ",", expr zero_comp, "]"] []))) (λ
   s, «expr $ »((cancel_mono a).1, by { rw [expr kernel_fork.ι_of_ι] ["at", ident ha'],
      simp [] [] [] ["[", expr ha', ",", expr pullback_cone.condition s, "]"] [] [] })) (λ
   s, «expr $ »((cancel_mono b).1, by { rw [expr kernel_fork.ι_of_ι] ["at", ident hb'],
      simp [] [] [] ["[", expr hb', "]"] [] [] })) (λ
   s
   m
   h₁
   h₂, «expr $ »((cancel_mono (kernel.ι (prod.lift f g))).1, calc
      «expr = »(«expr ≫ »(m, kernel.ι (prod.lift f g)), «expr ≫ »(m, «expr ≫ »(a', a))) : by { congr,
        exact [expr ha'.symm] }
      «expr = »(..., «expr ≫ »(pullback_cone.fst s, a)) : by rw ["[", "<-", expr category.assoc, ",", expr h₁, "]"] []
      «expr = »(..., «expr ≫ »(pullback_cone.snd s, b)) : pullback_cone.condition s
      «expr = »(..., «expr ≫ »(kernel.lift (prod.lift f g) «expr ≫ »(pullback_cone.snd s, b) _, kernel.ι (prod.lift f g))) : by rw [expr kernel.lift_ι] [])) }

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:927:38: unsupported irreducible non-definition
/-- The pushout of two epimorphisms exists. -/
@[irreducible]
theorem pushout_of_epi
{X Y Z : C}
(a : «expr ⟶ »(X, Y))
(b : «expr ⟶ »(X, Z))
[epi a]
[epi b] : has_colimit (span a b) :=
let ⟨P, f, hfa, i⟩ := non_preadditive_abelian.normal_epi a in
let ⟨Q, g, hgb, i'⟩ := non_preadditive_abelian.normal_epi b in
let ⟨a', ha'⟩ := «expr $ »(cokernel_cofork.is_colimit.desc' i (cokernel.π (coprod.desc f g)), calc
       «expr = »(«expr ≫ »(f, cokernel.π (coprod.desc f g)), «expr ≫ »(coprod.inl, «expr ≫ »(coprod.desc f g, cokernel.π (coprod.desc f g)))) : by rw [expr coprod.inl_desc_assoc] []
       «expr = »(..., «expr ≫ »(coprod.inl, (0 : «expr ⟶ »(«expr ⨿ »(P, Q), cokernel (coprod.desc f g))))) : by rw [expr cokernel.condition] []
       «expr = »(..., 0) : has_zero_morphisms.comp_zero _ _) in
let ⟨b', hb'⟩ := «expr $ »(cokernel_cofork.is_colimit.desc' i' (cokernel.π (coprod.desc f g)), calc
       «expr = »(«expr ≫ »(g, cokernel.π (coprod.desc f g)), «expr ≫ »(coprod.inr, «expr ≫ »(coprod.desc f g, cokernel.π (coprod.desc f g)))) : by rw [expr coprod.inr_desc_assoc] []
       «expr = »(..., «expr ≫ »(coprod.inr, (0 : «expr ⟶ »(«expr ⨿ »(P, Q), cokernel (coprod.desc f g))))) : by rw [expr cokernel.condition] []
       «expr = »(..., 0) : has_zero_morphisms.comp_zero _ _) in
has_colimit.mk { cocone := «expr $ »(pushout_cocone.mk a' b', by { simp [] [] ["only"] ["[", expr cofork.π_of_π, "]"] [] ["at", ident ha', ident hb'],
     rw ["[", expr ha', ",", expr hb', "]"] [] }),
  is_colimit := pushout_cocone.is_colimit.mk _ (λ
   s, «expr $ »(cokernel.desc (coprod.desc f g) «expr ≫ »(b, pushout_cocone.inr s), coprod.hom_ext (calc
       «expr = »(«expr ≫ »(coprod.inl, «expr ≫ »(coprod.desc f g, «expr ≫ »(b, pushout_cocone.inr s))), «expr ≫ »(f, «expr ≫ »(b, pushout_cocone.inr s))) : by rw [expr coprod.inl_desc_assoc] []
       «expr = »(..., «expr ≫ »(f, «expr ≫ »(a, pushout_cocone.inl s))) : by rw [expr pushout_cocone.condition] []
       «expr = »(..., «expr ≫ »(0, pushout_cocone.inl s)) : by rw [expr reassoc_of hfa] []
       «expr = »(..., «expr ≫ »(coprod.inl, 0)) : by rw ["[", expr comp_zero, ",", expr zero_comp, "]"] []) (calc
       «expr = »(«expr ≫ »(coprod.inr, «expr ≫ »(coprod.desc f g, «expr ≫ »(b, pushout_cocone.inr s))), «expr ≫ »(g, «expr ≫ »(b, pushout_cocone.inr s))) : by rw [expr coprod.inr_desc_assoc] []
       «expr = »(..., «expr ≫ »(0, pushout_cocone.inr s)) : by rw [expr reassoc_of hgb] []
       «expr = »(..., «expr ≫ »(coprod.inr, 0)) : by rw ["[", expr comp_zero, ",", expr zero_comp, "]"] []))) (λ
   s, «expr $ »((cancel_epi a).1, by { rw [expr cokernel_cofork.π_of_π] ["at", ident ha'],
      simp [] [] [] ["[", expr reassoc_of ha', ",", expr pushout_cocone.condition s, "]"] [] [] })) (λ
   s, «expr $ »((cancel_epi b).1, by { rw [expr cokernel_cofork.π_of_π] ["at", ident hb'],
      simp [] [] [] ["[", expr reassoc_of hb', "]"] [] [] })) (λ
   s
   m
   h₁
   h₂, «expr $ »((cancel_epi (cokernel.π (coprod.desc f g))).1, calc
      «expr = »(«expr ≫ »(cokernel.π (coprod.desc f g), m), «expr ≫ »(«expr ≫ »(a, a'), m)) : by { congr,
        exact [expr ha'.symm] }
      «expr = »(..., «expr ≫ »(a, pushout_cocone.inl s)) : by rw ["[", expr category.assoc, ",", expr h₁, "]"] []
      «expr = »(..., «expr ≫ »(b, pushout_cocone.inr s)) : pushout_cocone.condition s
      «expr = »(..., «expr ≫ »(cokernel.π (coprod.desc f g), cokernel.desc (coprod.desc f g) «expr ≫ »(b, pushout_cocone.inr s) _)) : by rw [expr cokernel.π_desc] [])) }

section 

attribute [local instance] pullback_of_mono

/-- The pullback of `(𝟙 X, f)` and `(𝟙 X, g)` -/
private abbrev P {X Y : C} (f g : X ⟶ Y) [mono (prod.lift (𝟙 X) f)] [mono (prod.lift (𝟙 X) g)] : C :=
  pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:927:38: unsupported irreducible non-definition
/-- The equalizer of `f` and `g` exists. -/
@[irreducible]
theorem has_limit_parallel_pair {X Y : C} (f g : «expr ⟶ »(X, Y)) : has_limit (parallel_pair f g) :=
have huv : «expr = »((pullback.fst : «expr ⟶ »(P f g, X)), pullback.snd), from calc
  «expr = »((pullback.fst : «expr ⟶ »(P f g, X)), «expr ≫ »(pullback.fst, «expr𝟙»() _)) : «expr $ »(eq.symm, category.comp_id _)
  «expr = »(..., «expr ≫ »(pullback.fst, «expr ≫ »(prod.lift («expr𝟙»() X) f, limits.prod.fst))) : by rw [expr prod.lift_fst] []
  «expr = »(..., «expr ≫ »(pullback.snd, «expr ≫ »(prod.lift («expr𝟙»() X) g, limits.prod.fst))) : by rw [expr pullback.condition_assoc] []
  «expr = »(..., pullback.snd) : by rw ["[", expr prod.lift_fst, ",", expr category.comp_id, "]"] [],
have hvu : «expr = »(«expr ≫ »((pullback.fst : «expr ⟶ »(P f g, X)), f), «expr ≫ »(pullback.snd, g)), from calc
  «expr = »(«expr ≫ »((pullback.fst : «expr ⟶ »(P f g, X)), f), «expr ≫ »(pullback.fst, «expr ≫ »(prod.lift («expr𝟙»() X) f, limits.prod.snd))) : by rw [expr prod.lift_snd] []
  «expr = »(..., «expr ≫ »(pullback.snd, «expr ≫ »(prod.lift («expr𝟙»() X) g, limits.prod.snd))) : by rw [expr pullback.condition_assoc] []
  «expr = »(..., «expr ≫ »(pullback.snd, g)) : by rw [expr prod.lift_snd] [],
have huu : «expr = »(«expr ≫ »((pullback.fst : «expr ⟶ »(P f g, X)), f), «expr ≫ »(pullback.fst, g)), by rw ["[", expr hvu, ",", "<-", expr huv, "]"] [],
has_limit.mk { cone := fork.of_ι pullback.fst huu,
  is_limit := fork.is_limit.mk _ (λ
   s, «expr $ »(pullback.lift (fork.ι s) (fork.ι s), prod.hom_ext (by simp [] [] ["only"] ["[", expr prod.lift_fst, ",", expr category.assoc, "]"] [] []) (by simp [] [] ["only"] ["[", expr fork.app_zero_right, ",", expr fork.app_zero_left, ",", expr prod.lift_snd, ",", expr category.assoc, "]"] [] []))) (λ
   s, by simp [] [] ["only"] ["[", expr fork.ι_of_ι, ",", expr pullback.lift_fst, "]"] [] []) (λ
   s
   m
   h, pullback.hom_ext (by simpa [] [] ["only"] ["[", expr pullback.lift_fst, "]"] [] ["using", expr h walking_parallel_pair.zero]) (by simpa [] [] ["only"] ["[", expr huv.symm, ",", expr pullback.lift_fst, "]"] [] ["using", expr h walking_parallel_pair.zero])) }

end 

section 

attribute [local instance] pushout_of_epi

/-- The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`. -/
private abbrev Q {X Y : C} (f g : X ⟶ Y) [epi (coprod.desc (𝟙 Y) f)] [epi (coprod.desc (𝟙 Y) g)] : C :=
  pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:927:38: unsupported irreducible non-definition
/-- The coequalizer of `f` and `g` exists. -/
@[irreducible]
theorem has_colimit_parallel_pair {X Y : C} (f g : «expr ⟶ »(X, Y)) : has_colimit (parallel_pair f g) :=
have huv : «expr = »((pushout.inl : «expr ⟶ »(Y, Q f g)), pushout.inr), from calc
  «expr = »((pushout.inl : «expr ⟶ »(Y, Q f g)), «expr ≫ »(«expr𝟙»() _, pushout.inl)) : «expr $ »(eq.symm, category.id_comp _)
  «expr = »(..., «expr ≫ »(«expr ≫ »(coprod.inl, coprod.desc («expr𝟙»() Y) f), pushout.inl)) : by rw [expr coprod.inl_desc] []
  «expr = »(..., «expr ≫ »(«expr ≫ »(coprod.inl, coprod.desc («expr𝟙»() Y) g), pushout.inr)) : by simp [] [] ["only"] ["[", expr category.assoc, ",", expr pushout.condition, "]"] [] []
  «expr = »(..., pushout.inr) : by rw ["[", expr coprod.inl_desc, ",", expr category.id_comp, "]"] [],
have hvu : «expr = »(«expr ≫ »(f, (pushout.inl : «expr ⟶ »(Y, Q f g))), «expr ≫ »(g, pushout.inr)), from calc
  «expr = »(«expr ≫ »(f, (pushout.inl : «expr ⟶ »(Y, Q f g))), «expr ≫ »(«expr ≫ »(coprod.inr, coprod.desc («expr𝟙»() Y) f), pushout.inl)) : by rw [expr coprod.inr_desc] []
  «expr = »(..., «expr ≫ »(«expr ≫ »(coprod.inr, coprod.desc («expr𝟙»() Y) g), pushout.inr)) : by simp [] [] ["only"] ["[", expr category.assoc, ",", expr pushout.condition, "]"] [] []
  «expr = »(..., «expr ≫ »(g, pushout.inr)) : by rw [expr coprod.inr_desc] [],
have huu : «expr = »(«expr ≫ »(f, (pushout.inl : «expr ⟶ »(Y, Q f g))), «expr ≫ »(g, pushout.inl)), by rw ["[", expr hvu, ",", expr huv, "]"] [],
has_colimit.mk { cocone := cofork.of_π pushout.inl huu,
  is_colimit := cofork.is_colimit.mk _ (λ
   s, «expr $ »(pushout.desc (cofork.π s) (cofork.π s), coprod.hom_ext (by simp [] [] ["only"] ["[", expr coprod.inl_desc_assoc, "]"] [] []) (by simp [] [] ["only"] ["[", expr cofork.right_app_one, ",", expr coprod.inr_desc_assoc, ",", expr cofork.left_app_one, "]"] [] []))) (λ
   s, by simp [] [] ["only"] ["[", expr pushout.inl_desc, ",", expr cofork.π_of_π, "]"] [] []) (λ
   s
   m
   h, pushout.hom_ext (by simpa [] [] ["only"] ["[", expr pushout.inl_desc, "]"] [] ["using", expr h walking_parallel_pair.one]) (by simpa [] [] ["only"] ["[", expr huv.symm, ",", expr pushout.inl_desc, "]"] [] ["using", expr h walking_parallel_pair.one])) }

end 

section 

attribute [local instance] has_limit_parallel_pair

/-- A `non_preadditive_abelian` category has all equalizers. -/
instance (priority := 100) has_equalizers : has_equalizers C :=
  has_equalizers_of_has_limit_parallel_pair _

end 

section 

attribute [local instance] has_colimit_parallel_pair

/-- A `non_preadditive_abelian` category has all coequalizers. -/
instance (priority := 100) has_coequalizers : has_coequalizers C :=
  has_coequalizers_of_has_colimit_parallel_pair _

end 

section 

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a zero morphism is a kernel of `f`, then `f` is a monomorphism. -/
theorem mono_of_zero_kernel
{X Y : C}
(f : «expr ⟶ »(X, Y))
(Z : C)
(l : is_limit (kernel_fork.of_ι (0 : «expr ⟶ »(Z, X)) (show «expr = »(«expr ≫ »(0, f), 0), by simp [] [] [] [] [] []))) : mono f :=
⟨λ P u v huv, begin
   obtain ["⟨", ident W, ",", ident w, ",", ident hw, ",", ident hl, "⟩", ":=", expr non_preadditive_abelian.normal_epi (coequalizer.π u v)],
   obtain ["⟨", ident m, ",", ident hm, "⟩", ":=", expr coequalizer.desc' f huv],
   have [ident hwf] [":", expr «expr = »(«expr ≫ »(w, f), 0)] [],
   { rw ["[", "<-", expr hm, ",", expr reassoc_of hw, ",", expr zero_comp, "]"] [] },
   obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr kernel_fork.is_limit.lift' l _ hwf],
   rw ["[", expr fork.ι_of_ι, ",", expr has_zero_morphisms.comp_zero, "]"] ["at", ident hn],
   haveI [] [":", expr is_iso (coequalizer.π u v)] [],
   { apply [expr is_iso_colimit_cocone_parallel_pair_of_eq hn.symm hl] },
   apply [expr (cancel_mono (coequalizer.π u v)).1],
   exact [expr coequalizer.condition _ _]
 end⟩

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a zero morphism is a cokernel of `f`, then `f` is an epimorphism. -/
theorem epi_of_zero_cokernel
{X Y : C}
(f : «expr ⟶ »(X, Y))
(Z : C)
(l : is_colimit (cokernel_cofork.of_π (0 : «expr ⟶ »(Y, Z)) (show «expr = »(«expr ≫ »(f, 0), 0), by simp [] [] [] [] [] []))) : epi f :=
⟨λ P u v huv, begin
   obtain ["⟨", ident W, ",", ident w, ",", ident hw, ",", ident hl, "⟩", ":=", expr non_preadditive_abelian.normal_mono (equalizer.ι u v)],
   obtain ["⟨", ident m, ",", ident hm, "⟩", ":=", expr equalizer.lift' f huv],
   have [ident hwf] [":", expr «expr = »(«expr ≫ »(f, w), 0)] [],
   { rw ["[", "<-", expr hm, ",", expr category.assoc, ",", expr hw, ",", expr comp_zero, "]"] [] },
   obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr cokernel_cofork.is_colimit.desc' l _ hwf],
   rw ["[", expr cofork.π_of_π, ",", expr zero_comp, "]"] ["at", ident hn],
   haveI [] [":", expr is_iso (equalizer.ι u v)] [],
   { apply [expr is_iso_limit_cone_parallel_pair_of_eq hn.symm hl] },
   apply [expr (cancel_epi (equalizer.ι u v)).1],
   exact [expr equalizer.condition _ _]
 end⟩

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

variable {P Q : C} (f : P ⟶ Q)

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

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The map `p : P ⟶ image f` is an epimorphism -/ instance : epi (non_preadditive_abelian.factor_thru_image f) :=
let I := non_preadditive_abelian.image f,
    p := non_preadditive_abelian.factor_thru_image f,
    i := kernel.ι (cokernel.π f) in
«expr $ »(epi_of_zero_cancel _, λ (R) (g : «expr ⟶ »(I, R)) (hpg : «expr = »(«expr ≫ »(p, g), 0)), begin
   let [ident u] [] [":=", expr «expr ≫ »(kernel.ι g, i)],
   haveI [] [":", expr mono u] [":=", expr mono_comp _ _],
   haveI [ident hu] [] [":=", expr non_preadditive_abelian.normal_mono u],
   let [ident h] [] [":=", expr hu.g],
   obtain ["⟨", ident t, ",", ident ht, "⟩", ":=", expr kernel.lift' g p hpg],
   have [ident fh] [":", expr «expr = »(«expr ≫ »(f, h), 0)] [],
   calc
     «expr = »(«expr ≫ »(f, h), «expr ≫ »(«expr ≫ »(p, i), h)) : «expr ▸ »((image.fac f).symm, rfl)
     «expr = »(..., «expr ≫ »(«expr ≫ »(«expr ≫ »(t, kernel.ι g), i), h)) : «expr ▸ »(ht, rfl)
     «expr = »(..., «expr ≫ »(t, «expr ≫ »(u, h))) : by simp [] [] ["only"] ["[", expr category.assoc, "]"] [] []; conv_lhs [] [] { congr,
       skip,
       rw ["<-", expr category.assoc] }
     «expr = »(..., «expr ≫ »(t, 0)) : «expr ▸ »(hu.w, rfl)
     «expr = »(..., 0) : has_zero_morphisms.comp_zero _ _,
   obtain ["⟨", ident l, ",", ident hl, "⟩", ":=", expr cokernel.desc' f h fh],
   have [ident hih] [":", expr «expr = »(«expr ≫ »(i, h), 0)] [],
   calc
     «expr = »(«expr ≫ »(i, h), «expr ≫ »(i, «expr ≫ »(cokernel.π f, l))) : «expr ▸ »(hl, rfl)
     «expr = »(..., «expr ≫ »(0, l)) : by rw ["[", "<-", expr category.assoc, ",", expr kernel.condition, "]"] []
     «expr = »(..., 0) : zero_comp,
   obtain ["⟨", ident s, ",", ident hs, "⟩", ":=", expr normal_mono.lift' u i hih],
   have [ident hs'] [":", expr «expr = »(«expr ≫ »(«expr ≫ »(s, kernel.ι g), i), «expr ≫ »(«expr𝟙»() I, i))] [],
   by rw ["[", expr category.assoc, ",", expr hs, ",", expr category.id_comp, "]"] [],
   haveI [] [":", expr epi (kernel.ι g)] [":=", expr epi_of_epi_fac ((cancel_mono _).1 hs')],
   exact [expr zero_of_epi_comp _ (kernel.condition g)]
 end)

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

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance : mono (non_preadditive_abelian.factor_thru_coimage f) :=
let I := non_preadditive_abelian.coimage f,
    i := non_preadditive_abelian.factor_thru_coimage f,
    p := cokernel.π (kernel.ι f) in
«expr $ »(mono_of_cancel_zero _, λ (R) (g : «expr ⟶ »(R, I)) (hgi : «expr = »(«expr ≫ »(g, i), 0)), begin
   let [ident u] [] [":=", expr «expr ≫ »(p, cokernel.π g)],
   haveI [] [":", expr epi u] [":=", expr epi_comp _ _],
   haveI [ident hu] [] [":=", expr non_preadditive_abelian.normal_epi u],
   let [ident h] [] [":=", expr hu.g],
   obtain ["⟨", ident t, ",", ident ht, "⟩", ":=", expr cokernel.desc' g i hgi],
   have [ident hf] [":", expr «expr = »(«expr ≫ »(h, f), 0)] [],
   calc
     «expr = »(«expr ≫ »(h, f), «expr ≫ »(h, «expr ≫ »(p, i))) : «expr ▸ »((coimage.fac f).symm, rfl)
     «expr = »(..., «expr ≫ »(h, «expr ≫ »(p, «expr ≫ »(cokernel.π g, t)))) : «expr ▸ »(ht, rfl)
     «expr = »(..., «expr ≫ »(h, «expr ≫ »(u, t))) : by simp [] [] ["only"] ["[", expr category.assoc, "]"] [] []; conv_lhs [] [] { congr,
       skip,
       rw ["<-", expr category.assoc] }
     «expr = »(..., «expr ≫ »(0, t)) : by rw ["[", "<-", expr category.assoc, ",", expr hu.w, "]"] []
     «expr = »(..., 0) : zero_comp,
   obtain ["⟨", ident l, ",", ident hl, "⟩", ":=", expr kernel.lift' f h hf],
   have [ident hhp] [":", expr «expr = »(«expr ≫ »(h, p), 0)] [],
   calc
     «expr = »(«expr ≫ »(h, p), «expr ≫ »(«expr ≫ »(l, kernel.ι f), p)) : «expr ▸ »(hl, rfl)
     «expr = »(..., «expr ≫ »(l, 0)) : by rw ["[", expr category.assoc, ",", expr cokernel.condition, "]"] []
     «expr = »(..., 0) : comp_zero,
   obtain ["⟨", ident s, ",", ident hs, "⟩", ":=", expr normal_epi.desc' u p hhp],
   have [ident hs'] [":", expr «expr = »(«expr ≫ »(p, «expr ≫ »(cokernel.π g, s)), «expr ≫ »(p, «expr𝟙»() I))] [],
   by rw ["[", "<-", expr category.assoc, ",", expr hs, ",", expr category.comp_id, "]"] [],
   haveI [] [":", expr mono (cokernel.π g)] [":=", expr mono_of_mono_fac ((cancel_epi _).1 hs')],
   exact [expr zero_of_comp_mono _ (cokernel.condition g)]
 end)

instance epi_factor_thru_coimage [epi f] : epi (non_preadditive_abelian.factor_thru_coimage f) :=
  epi_of_epi_fac$ coimage.fac f

instance is_iso_factor_thru_coimage [epi f] : is_iso (non_preadditive_abelian.factor_thru_coimage f) :=
  is_iso_of_mono_of_epi _

end Factor

section CokernelOfKernel

variable {X Y : C} {f : X ⟶ Y}

/-- In a `non_preadditive_abelian` category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel [epi f] (s : fork f 0) (h : is_limit s) :
  is_colimit (cokernel_cofork.of_π f (kernel_fork.condition s)) :=
  is_cokernel.cokernel_iso _ _
    (cokernel.of_iso_comp _ _ (limits.is_limit.cone_point_unique_up_to_iso (limit.is_limit _) h)
      (cone_morphism.w (limits.is_limit.unique_up_to_iso (limit.is_limit _) h).Hom _))
    (as_iso$ non_preadditive_abelian.factor_thru_coimage f) (coimage.fac f)

/-- In a `non_preadditive_abelian` category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def mono_is_kernel_of_cokernel [mono f] (s : cofork f 0) (h : is_colimit s) :
  is_limit (kernel_fork.of_ι f (cokernel_cofork.condition s)) :=
  is_kernel.iso_kernel _ _
    (kernel.of_comp_iso _ _ (limits.is_colimit.cocone_point_unique_up_to_iso h (colimit.is_colimit _))
      (cocone_morphism.w (limits.is_colimit.unique_up_to_iso h$ colimit.is_colimit _).Hom _))
    (as_iso$ non_preadditive_abelian.factor_thru_image f) (image.fac f)

end CokernelOfKernel

section 

/-- The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` and the second map
    is the canonical projection into the cokernel. -/
abbrev r (A : C) : A ⟶ cokernel (diag A) :=
  prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)

instance mono_Δ {A : C} : mono (diag A) :=
  mono_of_mono_fac$ prod.lift_fst _ _

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance mono_r {A : C} : mono (r A) :=
begin
  let [ident hl] [":", expr is_limit (kernel_fork.of_ι (diag A) (cokernel.condition (diag A)))] [],
  { exact [expr mono_is_kernel_of_cokernel _ (colimit.is_colimit _)] },
  apply [expr mono_of_cancel_zero],
  intros [ident Z, ident x, ident hx],
  have [ident hxx] [":", expr «expr = »(«expr ≫ »(«expr ≫ »(x, prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A))), cokernel.π (diag A)), 0)] [],
  { rw ["[", expr category.assoc, ",", expr hx, "]"] [] },
  obtain ["⟨", ident y, ",", ident hy, "⟩", ":=", expr kernel_fork.is_limit.lift' hl _ hxx],
  rw [expr kernel_fork.ι_of_ι] ["at", ident hy],
  have [ident hyy] [":", expr «expr = »(y, 0)] [],
  { erw ["[", "<-", expr category.comp_id y, ",", "<-", expr limits.prod.lift_snd («expr𝟙»() A) («expr𝟙»() A), ",", "<-", expr category.assoc, ",", expr hy, ",", expr category.assoc, ",", expr prod.lift_snd, ",", expr has_zero_morphisms.comp_zero, "]"] [] },
  haveI [] [":", expr mono (prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A)))] [":=", expr mono_of_mono_fac (prod.lift_fst _ _)],
  apply [expr (cancel_mono (prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A)))).1],
  rw ["[", "<-", expr hy, ",", expr hyy, ",", expr zero_comp, ",", expr zero_comp, "]"] []
end

-- error in CategoryTheory.Abelian.NonPreadditive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance epi_r {A : C} : epi (r A) :=
begin
  have [ident hlp] [":", expr «expr = »(«expr ≫ »(prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A)), limits.prod.snd), 0)] [":=", expr prod.lift_snd _ _],
  let [ident hp1] [":", expr is_limit (kernel_fork.of_ι (prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A))) hlp)] [],
  { refine [expr fork.is_limit.mk _ (λ s, «expr ≫ »(fork.ι s, limits.prod.fst)) _ _],
    { intro [ident s],
      ext [] [] []; simp [] [] [] [] [] [],
      erw [expr category.comp_id] [] },
    { intros [ident s, ident m, ident h],
      haveI [] [":", expr mono (prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A)))] [":=", expr mono_of_mono_fac (prod.lift_fst _ _)],
      apply [expr (cancel_mono (prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A)))).1],
      convert [] [expr h walking_parallel_pair.zero] [],
      ext [] [] []; simp [] [] [] [] [] [] } },
  let [ident hp2] [":", expr is_colimit (cokernel_cofork.of_π (limits.prod.snd : «expr ⟶ »(«expr ⨯ »(A, A), A)) hlp)] [],
  { exact [expr epi_is_cokernel_of_kernel _ hp1] },
  apply [expr epi_of_zero_cancel],
  intros [ident Z, ident z, ident hz],
  have [ident h] [":", expr «expr = »(«expr ≫ »(prod.lift («expr𝟙»() A) (0 : «expr ⟶ »(A, A)), «expr ≫ »(cokernel.π (diag A), z)), 0)] [],
  { rw ["[", "<-", expr category.assoc, ",", expr hz, "]"] [] },
  obtain ["⟨", ident t, ",", ident ht, "⟩", ":=", expr cokernel_cofork.is_colimit.desc' hp2 _ h],
  rw [expr cokernel_cofork.π_of_π] ["at", ident ht],
  have [ident htt] [":", expr «expr = »(t, 0)] [],
  { rw ["[", "<-", expr category.id_comp t, "]"] [],
    change [expr «expr = »(«expr ≫ »(«expr𝟙»() A, t), 0)] [] [],
    rw ["[", "<-", expr limits.prod.lift_snd («expr𝟙»() A) («expr𝟙»() A), ",", expr category.assoc, ",", expr ht, ",", "<-", expr category.assoc, ",", expr cokernel.condition, ",", expr zero_comp, "]"] [] },
  apply [expr (cancel_epi (cokernel.π (diag A))).1],
  rw ["[", "<-", expr ht, ",", expr htt, ",", expr comp_zero, ",", expr comp_zero, "]"] []
end

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

