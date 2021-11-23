import Mathbin.Algebra.Homology.ImageToKernel

/-!
# Exact sequences

In a category with zero morphisms, images, and equalizers we say that `f : A ⟶ B` and `g : B ⟶ C`
are exact if `f ≫ g = 0` and the natural map `image f ⟶ kernel g` is an epimorphism.

In any preadditive category this is equivalent to the homology at `B` vanishing.

However in general it is weaker than other reasonable definitions of exactness,
particularly that
1. the inclusion map `image.ι f` is a kernel of `g` or
2. `image f ⟶ kernel g` is an isomorphism or
3. `image_subobject f = kernel_subobject f`.
However when the category is abelian, these all become equivalent;
these results are found in `category_theory/abelian/exact.lean`.

# Main results
* Suppose that cokernels exist and that `f` and `g` are exact.
  If `s` is any kernel fork over `g` and `t` is any cokernel cofork over `f`,
  then `fork.ι s ≫ cofork.π t = 0`.
* Precomposing the first morphism with an epimorphism retains exactness.
  Postcomposing the second morphism with a monomorphism retains exactness.
* If `f` and `g` are exact and `i` is an isomorphism,
  then `f ≫ i.hom` and `i.inv ≫ g` are also exact.

# Future work
* Short exact sequences, split exact sequences, the splitting lemma (maybe only for abelian
  categories?)
* Two adjacent maps in a chain complex are exact iff the homology vanishes

-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

variable{V : Type u}[category.{v} V]

variable[has_images V]

namespace CategoryTheory

/--
Two morphisms `f : A ⟶ B`, `g : B ⟶ C` are called exact if `w : f ≫ g = 0` and the natural map
`image_to_kernel f g w : image_subobject f ⟶ kernel_subobject g` is an epimorphism.

In any preadditive category, this is equivalent to `w : f ≫ g = 0` and `homology f g w ≅ 0`.

In an abelian category, this is equivalent to `image_to_kernel f g w` being an isomorphism,
and hence equivalent to the usual definition,
`image_subobject f = kernel_subobject g`.
-/
class exact[has_zero_morphisms V][has_kernels V]{A B C : V}(f : A ⟶ B)(g : B ⟶ C) : Prop where 
  w : f ≫ g = 0 
  Epi : epi (imageToKernel f g w)

attribute [instance] exact.epi

attribute [simp, reassoc] exact.w

section 

variable[has_zero_object V][preadditive V][has_kernels V][has_cokernels V]

open_locale ZeroObject

/--
In any preadditive category,
composable morphisms `f g` are exact iff they compose to zero and the homology vanishes.
-/
theorem preadditive.exact_iff_homology_zero {A B C : V} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ ∃ w : f ≫ g = 0, Nonempty (homology f g w ≅ 0) :=
  ⟨fun h => ⟨h.w, ⟨cokernel.of_epi _⟩⟩,
    fun h =>
      by 
        obtain ⟨w, ⟨i⟩⟩ := h 
        exact
          ⟨w,
            preadditive.epi_of_cokernel_zero
              ((cancel_mono i.hom).mp
                (by 
                  ext))⟩⟩

theorem preadditive.exact_of_iso_of_exact {A₁ B₁ C₁ A₂ B₂ C₂ : V} (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂)
  (g₂ : B₂ ⟶ C₂) (α : arrow.mk f₁ ≅ arrow.mk f₂) (β : arrow.mk g₁ ≅ arrow.mk g₂) (p : α.hom.right = β.hom.left)
  (h : exact f₁ g₁) : exact f₂ g₂ :=
  by 
    rw [preadditive.exact_iff_homology_zero] at h⊢
    rcases h with ⟨w₁, ⟨i⟩⟩
    suffices w₂ : f₂ ≫ g₂ = 0 
    exact ⟨w₂, ⟨(homology.mapIso w₁ w₂ α β p).symm.trans i⟩⟩
    rw [←cancel_epi α.hom.left, ←cancel_mono β.inv.right, comp_zero, zero_comp, ←w₁]
    simp only [←arrow.mk_hom f₁, ←arrow.left_hom_inv_right α.hom, ←arrow.mk_hom g₁, ←arrow.left_hom_inv_right β.hom, p]
    simp only [arrow.mk_hom, is_iso.inv_hom_id_assoc, category.assoc, ←arrow.inv_right, is_iso.iso.inv_hom]

theorem preadditive.exact_iff_exact_of_iso {A₁ B₁ C₁ A₂ B₂ C₂ : V} (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂)
  (g₂ : B₂ ⟶ C₂) (α : arrow.mk f₁ ≅ arrow.mk f₂) (β : arrow.mk g₁ ≅ arrow.mk g₂) (p : α.hom.right = β.hom.left) :
  exact f₁ g₁ ↔ exact f₂ g₂ :=
  ⟨preadditive.exact_of_iso_of_exact _ _ _ _ _ _ p,
    preadditive.exact_of_iso_of_exact _ _ _ _ α.symm β.symm
      (by 
        rw [←cancel_mono α.hom.right]
        simp only [iso.symm_hom, ←comma.comp_right, α.inv_hom_id]
        simp only [p, ←comma.comp_left, arrow.id_right, arrow.id_left, iso.inv_hom_id]
        rfl)⟩

end 

section 

variable[has_zero_morphisms V][has_kernels V]

theorem comp_eq_zero_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  (p : image_subobject f = kernel_subobject g) : f ≫ g = 0 :=
  by 
    rw [←image_subobject_arrow_comp f, category.assoc]
    convert comp_zero 
    rw [p]
    simp 

theorem image_to_kernel_is_iso_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  (p : image_subobject f = kernel_subobject g) : is_iso (imageToKernel f g (comp_eq_zero_of_image_eq_kernel f g p)) :=
  by 
    refine' ⟨⟨subobject.of_le _ _ p.ge, _⟩⟩
    dsimp [imageToKernel]
    simp only [subobject.of_le_comp_of_le, subobject.of_le_refl]
    simp 

-- error in Algebra.Homology.Exact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exact_of_image_eq_kernel
{A B C : V}
(f : «expr ⟶ »(A, B))
(g : «expr ⟶ »(B, C))
(p : «expr = »(image_subobject f, kernel_subobject g)) : exact f g :=
{ w := comp_eq_zero_of_image_eq_kernel f g p,
  epi := begin
    haveI [] [] [":=", expr image_to_kernel_is_iso_of_image_eq_kernel f g p],
    apply_instance
  end }

end 

variable{A B C D : V}{f : A ⟶ B}{g : B ⟶ C}{h : C ⟶ D}

attribute [local instance] epi_comp

section 

variable[has_zero_morphisms V][has_equalizers V]

instance exact_comp_hom_inv_comp [exact f g] (i : B ≅ D) : exact (f ≫ i.hom) (i.inv ≫ g) :=
  by 
    refine'
      ⟨by 
          simp ,
        _⟩
    rw [image_to_kernel_comp_hom_inv_comp]
    infer_instance

instance exact_comp_inv_hom_comp [exact f g] (i : D ≅ B) : exact (f ≫ i.inv) (i.hom ≫ g) :=
  CategoryTheory.exact_comp_hom_inv_comp i.symm

-- error in Algebra.Homology.Exact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exact_comp_hom_inv_comp_iff
(i : «expr ≅ »(B, D)) : «expr ↔ »(exact «expr ≫ »(f, i.hom) «expr ≫ »(i.inv, g), exact f g) :=
begin
  refine [expr ⟨_, by { introI [], apply_instance }⟩],
  introI [],
  have [] [":", expr exact «expr ≫ »(«expr ≫ »(f, i.hom), i.inv) «expr ≫ »(i.hom, «expr ≫ »(i.inv, g))] [":=", expr infer_instance],
  simpa [] [] [] [] [] ["using", expr this]
end

theorem exact_epi_comp [exact g h] [epi f] : exact (f ≫ g) h :=
  by 
    refine'
      ⟨by 
          simp ,
        _⟩
    rw [image_to_kernel_comp_left]
    infer_instance

@[simp]
theorem exact_iso_comp [is_iso f] : exact (f ≫ g) h ↔ exact g h :=
  ⟨fun w =>
      by 
        rw [←is_iso.inv_hom_id_assoc f g]
        exact exact_epi_comp,
    fun w =>
      by 
        exact exact_epi_comp⟩

theorem exact_comp_mono [exact f g] [mono h] : exact f (g ≫ h) :=
  by 
    refine'
      ⟨by 
          simp ,
        _⟩
    rw [image_to_kernel_comp_right f g h exact.w]
    infer_instance

@[simp]
theorem exact_comp_iso [is_iso h] : exact f (g ≫ h) ↔ exact f g :=
  ⟨fun w =>
      by 
        rw [←category.comp_id g, ←is_iso.hom_inv_id h, ←category.assoc]
        exact exact_comp_mono,
    fun w =>
      by 
        exact exact_comp_mono⟩

theorem exact_kernel_subobject_arrow : exact (kernel_subobject f).arrow f :=
  by 
    refine'
      ⟨by 
          simp ,
        _⟩
    apply @is_iso.epi_of_iso _ _ _ _ _ _ 
    exact
      ⟨⟨factor_thru_image_subobject _,
          by 
            ext 
            simp ,
          by 
            ext 
            simp ⟩⟩

theorem exact_kernel_ι : exact (kernel.ι f) f :=
  by 
    rw [←kernel_subobject_arrow', exact_iso_comp]
    exact exact_kernel_subobject_arrow

instance  [exact f g] :
  epi
    (factor_thru_kernel_subobject g f
      (by 
        simp )) :=
  by 
    rw [←factor_thru_image_subobject_comp_image_to_kernel]
    apply epi_comp

instance  [exact f g] :
  epi
    (kernel.lift g f
      (by 
        simp )) :=
  by 
    rw [←factor_thru_kernel_subobject_comp_kernel_subobject_iso]
    apply epi_comp

variable(A)

theorem kernel_subobject_arrow_eq_zero_of_exact_zero_left [exact (0 : A ⟶ B) g] : (kernel_subobject g).arrow = 0 :=
  by 
    rw [←cancel_epi (imageToKernel (0 : A ⟶ B) g exact.w), ←cancel_epi (factor_thru_image_subobject (0 : A ⟶ B))]
    simp 

theorem kernel_ι_eq_zero_of_exact_zero_left [exact (0 : A ⟶ B) g] : kernel.ι g = 0 :=
  by 
    rw [←kernel_subobject_arrow']
    simp [kernel_subobject_arrow_eq_zero_of_exact_zero_left A]

theorem exact_zero_left_of_mono [has_zero_object V] [mono g] : exact (0 : A ⟶ B) g :=
  ⟨by 
      simp ,
    image_to_kernel_epi_of_zero_of_mono _⟩

end 

section HasCokernels

variable[has_zero_morphisms V][has_equalizers V][has_cokernels V](f g)

@[simp, reassoc]
theorem kernel_comp_cokernel [exact f g] : kernel.ι g ≫ cokernel.π f = 0 :=
  by 
    rw [←kernel_subobject_arrow', category.assoc]
    convert comp_zero 
    apply zero_of_epi_comp (imageToKernel f g exact.w) _ 
    rw [image_to_kernel_arrow_assoc, ←image_subobject_arrow, category.assoc, ←iso.eq_inv_comp]
    ext 
    simp 

theorem comp_eq_zero_of_exact [exact f g] {X Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y} (hπ : f ≫ π = 0) :
  ι ≫ π = 0 :=
  by 
    rw [←kernel.lift_ι _ _ hι, ←cokernel.π_desc _ _ hπ, category.assoc, kernel_comp_cokernel_assoc, zero_comp,
      comp_zero]

@[simp, reassoc]
theorem fork_ι_comp_cofork_π [exact f g] (s : kernel_fork g) (t : cokernel_cofork f) : fork.ι s ≫ cofork.π t = 0 :=
  comp_eq_zero_of_exact f g (kernel_fork.condition s) (cokernel_cofork.condition t)

end HasCokernels

section 

variable[has_zero_object V]

open_locale ZeroObject

section 

variable[has_zero_morphisms V][has_kernels V]

instance exact_of_zero {A C : V} (f : A ⟶ 0) (g : 0 ⟶ C) : exact f g :=
  by 
    obtain rfl : f = 0 :=
      by 
        ext 
    obtain rfl : g = 0 :=
      by 
        ext 
    fsplit
    ·
      simp 
    ·
      exact image_to_kernel_epi_of_zero_of_mono 0

instance exact_zero_mono {B C : V} (f : B ⟶ C) [mono f] : exact (0 : 0 ⟶ B) f :=
  ⟨by 
      simp ,
    inferInstance⟩

instance exact_epi_zero {A B : V} (f : A ⟶ B) [epi f] : exact f (0 : B ⟶ 0) :=
  ⟨by 
      simp ,
    inferInstance⟩

end 

section 

variable[preadditive V]

theorem mono_iff_exact_zero_left [has_kernels V] {B C : V} (f : B ⟶ C) : mono f ↔ exact (0 : 0 ⟶ B) f :=
  ⟨fun h =>
      by 
        skip 
        infer_instance,
    fun h =>
      preadditive.mono_of_kernel_iso_zero
        ((kernel_subobject_iso f).symm ≪≫
          iso_zero_of_epi_zero
            (by 
              simpa using h.epi))⟩

-- error in Algebra.Homology.Exact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem epi_iff_exact_zero_right
[has_equalizers V]
{A B : V}
(f : «expr ⟶ »(A, B)) : «expr ↔ »(epi f, exact f (0 : «expr ⟶ »(B, 0))) :=
⟨λ h, by { resetI,
   apply_instance }, λ h, begin
   have [ident e₁] [] [":=", expr h.epi],
   rw [expr image_to_kernel_zero_right] ["at", ident e₁],
   have [ident e₂] [":", expr epi «expr ≫ »(«expr ≫ »((image_subobject f).arrow, inv (kernel_subobject 0).arrow), (kernel_subobject 0).arrow)] [":=", expr @epi_comp _ _ _ _ _ _ e₁ _ _],
   rw ["[", expr category.assoc, ",", expr is_iso.inv_hom_id, ",", expr category.comp_id, "]"] ["at", ident e₂],
   rw ["[", "<-", expr image_subobject_arrow, "]"] ["at", ident e₂],
   resetI,
   haveI [] [":", expr epi (image.ι f)] [":=", expr epi_of_epi (image_subobject_iso f).hom (image.ι f)],
   apply [expr epi_of_epi_image]
 end⟩

end 

end 

end CategoryTheory

