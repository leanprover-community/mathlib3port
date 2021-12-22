import Mathbin.CategoryTheory.Subobject.Limits

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : image_subobject f ≤ kernel_subobject g`
(assuming the appropriate images and kernels exist).

`image_to_kernel f g w` is the corresponding morphism between objects in `C`.

We define `homology f g w` of such a pair as the cokernel of `image_to_kernel f g w`.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable {ι : Type _}

variable {V : Type u} [category.{v} V] [has_zero_morphisms V]

open_locale Classical

noncomputable section

section

variable {A B C : V} (f : A ⟶ B) [has_image f] (g : B ⟶ C) [has_kernel g]

theorem image_le_kernel (w : f ≫ g = 0) : image_subobject f ≤ kernel_subobject g :=
  image_subobject_le_mk _ _ (kernel.lift _ _ w)
    (by
      simp )

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler mono
/-- 
The canonical morphism `image_subobject f ⟶ kernel_subobject g` when `f ≫ g = 0`.
-/
def imageToKernel (w : f ≫ g = 0) : (image_subobject f : V) ⟶ (kernel_subobject g : V) :=
  subobject.of_le _ _ (image_le_kernel _ _ w)deriving [anonymous]

/--  Prefer `image_to_kernel`. -/
@[simp]
theorem subobject_of_le_as_image_to_kernel (w : f ≫ g = 0) h :
    subobject.of_le (image_subobject f) (kernel_subobject g) h = imageToKernel f g w :=
  rfl

@[simp, reassoc]
theorem image_to_kernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernel_subobject g).arrow = (image_subobject f).arrow := by
  simp [imageToKernel]

theorem factor_thru_image_subobject_comp_image_to_kernel (w : f ≫ g = 0) :
    factor_thru_image_subobject f ≫ imageToKernel f g w = factor_thru_kernel_subobject g f w := by
  ext
  simp

end

section

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
theorem image_to_kernel_zero_left [has_kernels V] [has_zero_object V] {w} : imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp

theorem image_to_kernel_zero_right [has_images V] {w} :
    imageToKernel f (0 : B ⟶ C) w = (image_subobject f).arrow ≫ inv (kernel_subobject (0 : B ⟶ C)).arrow := by
  ext
  simp

section

variable [has_kernels V] [has_images V]

theorem image_to_kernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    imageToKernel f (g ≫ h)
        (by
          simp [reassoc_of w]) =
      imageToKernel f g w ≫ subobject.of_le _ _ (kernel_subobject_comp_le g h) :=
  by
  ext
  simp

theorem image_to_kernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    imageToKernel (h ≫ f) g
        (by
          simp [w]) =
      subobject.of_le _ _ (image_subobject_comp_le h f) ≫ imageToKernel f g w :=
  by
  ext
  simp

@[simp]
theorem image_to_kernel_comp_mono {D : V} (h : C ⟶ D) [mono h] w :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g
          ((cancel_mono h).mp
            (by
              simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (subobject.iso_of_eq _ _ (kernel_subobject_comp_mono g h)).inv :=
  by
  ext
  simp

@[simp]
theorem image_to_kernel_epi_comp {Z : V} (h : Z ⟶ A) [epi h] w :
    imageToKernel (h ≫ f) g w =
      subobject.of_le _ _ (image_subobject_comp_le h f) ≫
        imageToKernel f g
          ((cancel_epi h).mp
            (by
              simpa using w : h ≫ f ≫ g = h ≫ 0)) :=
  by
  ext
  simp

end

@[simp]
theorem image_to_kernel_comp_hom_inv_comp [has_equalizers V] [has_images V] {Z : V} {i : B ≅ Z} w :
    imageToKernel (f ≫ i.hom) (i.inv ≫ g) w =
      (image_subobject_comp_iso _ _).Hom ≫
        imageToKernel f g
            (by
              simpa using w) ≫
          (kernel_subobject_iso_comp i.inv g).inv :=
  by
  ext
  simp

open_locale ZeroObject

/-- 
`image_to_kernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance image_to_kernel_epi_of_zero_of_mono [has_kernels V] [has_zero_object V] [mono g] :
    epi
      (imageToKernel (0 : A ⟶ B) g
        (by
          simp )) :=
  epi_of_target_iso_zero _ (kernel_subobject_iso g ≪≫ kernel.of_mono g)

/-- 
`image_to_kernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance image_to_kernel_epi_of_epi_of_zero [has_images V] [epi f] :
    epi
      (imageToKernel f (0 : B ⟶ C)
        (by
          simp )) :=
  by
  simp only [image_to_kernel_zero_right]
  have := epi_image_of_epi f
  rw [← image_subobject_arrow]
  refine' @epi_comp _ _ _ _ _ _ (epi_comp _ _) _ _

end

section

variable {A B C : V} (f : A ⟶ B) [has_image f] (g : B ⟶ C) [has_kernel g]

/-- 
The homology of a pair of morphisms `f : A ⟶ B` and `g : B ⟶ C` satisfying `f ≫ g = 0`
is the cokernel of the `image_to_kernel` morphism for `f` and `g`.
-/
def homology {A B C : V} (f : A ⟶ B) [has_image f] (g : B ⟶ C) [has_kernel g] (w : f ≫ g = 0)
    [has_cokernel (imageToKernel f g w)] : V :=
  cokernel (imageToKernel f g w)

section

variable (w : f ≫ g = 0) [has_cokernel (imageToKernel f g w)]

/--  The morphism from cycles to homology. -/
def homology.π : (kernel_subobject g : V) ⟶ homology f g w :=
  cokernel.π _

@[simp]
theorem homology.condition : imageToKernel f g w ≫ homology.π f g w = 0 :=
  cokernel.condition _

/-- 
To construct a map out of homology, it suffices to construct a map out of the cycles
which vanishes on boundaries.
-/
def homology.desc {D : V} (k : (kernel_subobject g : V) ⟶ D) (p : imageToKernel f g w ≫ k = 0) : homology f g w ⟶ D :=
  cokernel.desc _ k p

@[simp, reassoc]
theorem homology.π_desc {D : V} (k : (kernel_subobject g : V) ⟶ D) (p : imageToKernel f g w ≫ k = 0) :
    homology.π f g w ≫ homology.desc f g w k p = k := by
  simp [homology.π, homology.desc]

/--  To check two morphisms out of `homology f g w` are equal, it suffices to check on cycles. -/
@[ext]
theorem homology.ext {D : V} {k k' : homology f g w ⟶ D} (p : homology.π f g w ≫ k = homology.π f g w ≫ k') : k = k' :=
  by
  ext
  exact p

/--  `homology 0 0 _` is just the middle object. -/
@[simps]
def homologyZeroZero [has_zero_object V] [has_image (0 : A ⟶ B)]
    [has_cokernel
        (imageToKernel (0 : A ⟶ B) (0 : B ⟶ C)
          (by
            simp ))] :
    homology (0 : A ⟶ B) (0 : B ⟶ C)
        (by
          simp ) ≅
      B :=
  { Hom :=
      homology.desc (0 : A ⟶ B) (0 : B ⟶ C)
        (by
          simp )
        (kernel_subobject 0).arrow
        (by
          simp ),
    inv := inv (kernel_subobject 0).arrow ≫ homology.π _ _ _ }

end

section

variable {f g} (w : f ≫ g = 0) {A' B' C' : V} {f' : A' ⟶ B'} [has_image f'] {g' : B' ⟶ C'} [has_kernel g']
  (w' : f' ≫ g' = 0) (α : arrow.mk f ⟶ arrow.mk f') [has_image_map α] (β : arrow.mk g ⟶ arrow.mk g') {A₁ B₁ C₁ : V}
  {f₁ : A₁ ⟶ B₁} [has_image f₁] {g₁ : B₁ ⟶ C₁} [has_kernel g₁] (w₁ : f₁ ≫ g₁ = 0) {A₂ B₂ C₂ : V} {f₂ : A₂ ⟶ B₂}
  [has_image f₂] {g₂ : B₂ ⟶ C₂} [has_kernel g₂] (w₂ : f₂ ≫ g₂ = 0) {A₃ B₃ C₃ : V} {f₃ : A₃ ⟶ B₃} [has_image f₃]
  {g₃ : B₃ ⟶ C₃} [has_kernel g₃] (w₃ : f₃ ≫ g₃ = 0) (α₁ : arrow.mk f₁ ⟶ arrow.mk f₂) [has_image_map α₁]
  (β₁ : arrow.mk g₁ ⟶ arrow.mk g₂) (α₂ : arrow.mk f₂ ⟶ arrow.mk f₃) [has_image_map α₂] (β₂ : arrow.mk g₂ ⟶ arrow.mk g₃)

/-- 
Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
the `image_to_kernel` morphisms intertwine the induced map on kernels and the induced map on images.
-/
@[reassoc]
theorem image_subobject_map_comp_image_to_kernel (p : α.right = β.left) :
    imageToKernel f g w ≫ kernel_subobject_map β = image_subobject_map α ≫ imageToKernel f' g' w' := by
  ext
  simp [p]

variable [has_cokernel (imageToKernel f g w)] [has_cokernel (imageToKernel f' g' w')]

variable [has_cokernel (imageToKernel f₁ g₁ w₁)]

variable [has_cokernel (imageToKernel f₂ g₂ w₂)]

variable [has_cokernel (imageToKernel f₃ g₃ w₃)]

/-- 
Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
we get a morphism on homology.
-/
def homology.map (p : α.right = β.left) : homology f g w ⟶ homology f' g' w' :=
  cokernel.desc _ (kernel_subobject_map β ≫ cokernel.π _)
    (by
      rw [image_subobject_map_comp_image_to_kernel_assoc w w' α β p]
      simp only [cokernel.condition, comp_zero])

@[simp, reassoc]
theorem homology.π_map (p : α.right = β.left) :
    homology.π f g w ≫ homology.map w w' α β p = kernel_subobject_map β ≫ homology.π f' g' w' := by
  simp only [homology.π, homology.map, cokernel.π_desc]

@[simp, reassoc]
theorem homology.map_desc (p : α.right = β.left) {D : V} (k : (kernel_subobject g' : V) ⟶ D)
    (z : imageToKernel f' g' w' ≫ k = 0) :
    homology.map w w' α β p ≫ homology.desc f' g' w' k z =
      homology.desc f g w (kernel_subobject_map β ≫ k)
        (by
          simp only [image_subobject_map_comp_image_to_kernel_assoc w w' α β p, z, comp_zero]) :=
  by
  ext <;> simp only [homology.π_desc, homology.π_map_assoc]

@[simp]
theorem homology.map_id : homology.map w w (𝟙 _) (𝟙 _) rfl = 𝟙 _ := by
  ext <;> simp only [homology.π_map, kernel_subobject_map_id, category.id_comp, category.comp_id]

/--  Auxiliary lemma for homology computations. -/
theorem homology.comp_right_eq_comp_left {V : Type _} [category V] {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : V} {f₁ : A₁ ⟶ B₁}
    {g₁ : B₁ ⟶ C₁} {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} {f₃ : A₃ ⟶ B₃} {g₃ : B₃ ⟶ C₃} {α₁ : arrow.mk f₁ ⟶ arrow.mk f₂}
    {β₁ : arrow.mk g₁ ⟶ arrow.mk g₂} {α₂ : arrow.mk f₂ ⟶ arrow.mk f₃} {β₂ : arrow.mk g₂ ⟶ arrow.mk g₃}
    (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) : (α₁ ≫ α₂).right = (β₁ ≫ β₂).left := by
  simp only [comma.comp_left, comma.comp_right, p₁, p₂]

@[reassoc]
theorem homology.map_comp (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) :
    homology.map w₁ w₂ α₁ β₁ p₁ ≫ homology.map w₂ w₃ α₂ β₂ p₂ =
      homology.map w₁ w₃ (α₁ ≫ α₂) (β₁ ≫ β₂) (homology.comp_right_eq_comp_left p₁ p₂) :=
  by
  ext <;> simp only [kernel_subobject_map_comp, homology.π_map_assoc, homology.π_map, category.assoc]

/--  An isomorphism between two three-term complexes induces an isomorphism on homology. -/
def homology.mapIso (α : arrow.mk f₁ ≅ arrow.mk f₂) (β : arrow.mk g₁ ≅ arrow.mk g₂) (p : α.hom.right = β.hom.left) :
    homology f₁ g₁ w₁ ≅ homology f₂ g₂ w₂ :=
  { Hom := homology.map w₁ w₂ α.hom β.hom p,
    inv :=
      homology.map w₂ w₁ α.inv β.inv
        (by
          rw [← cancel_mono α.hom.right, ← comma.comp_right, α.inv_hom_id, comma.id_right, p, ← comma.comp_left,
            β.inv_hom_id, comma.id_left]
          rfl),
    hom_inv_id' := by
      rw [homology.map_comp]
      convert homology.map_id _ <;> rw [iso.hom_inv_id],
    inv_hom_id' := by
      rw [homology.map_comp]
      convert homology.map_id _ <;> rw [iso.inv_hom_id] }

end

end

section

variable {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) {f' : A ⟶ B} {g' : B ⟶ C} (w' : f' ≫ g' = 0)
  [has_kernels V] [has_cokernels V] [has_images V] [has_image_maps V]

-- ././Mathport/Syntax/Translate/Basic.lean:771:4: warning: unsupported (TODO): `[tacs]
/--  Custom tactic to golf and speedup boring proofs in `homology.congr`. -/
private unsafe def aux_tac : tactic Unit :=
  sorry

/-- 
`homology f g w ≅ homology f' g' w'` if `f = f'` and `g = g'`.
(Note the objects are not changing here.)
-/
@[simps]
def homology.congr (pf : f = f') (pg : g = g') : homology f g w ≅ homology f' g' w' :=
  { Hom :=
      homology.map w w'
        ⟨𝟙 _, 𝟙 _, by
          run_tac
            aux_tac⟩
        ⟨𝟙 _, 𝟙 _, by
          run_tac
            aux_tac⟩
        rfl,
    inv :=
      homology.map w' w
        ⟨𝟙 _, 𝟙 _, by
          run_tac
            aux_tac⟩
        ⟨𝟙 _, 𝟙 _, by
          run_tac
            aux_tac⟩
        rfl,
    hom_inv_id' := by
      cases pf
      cases pg
      rw [homology.map_comp, ← homology.map_id]
      congr 1 <;> exact category.comp_id _,
    inv_hom_id' := by
      cases pf
      cases pg
      rw [homology.map_comp, ← homology.map_id]
      congr 1 <;> exact category.comp_id _ }

end

/-!
We provide a variant `image_to_kernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/


section imageToKernel'

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) [has_kernels V] [has_images V]

/-- 
While `image_to_kernel f g w` provides a morphism
`image_subobject f ⟶ kernel_subobject g`
in terms of the subobject API,
this variant provides a morphism
`image f ⟶ kernel g`,
which is sometimes more convenient.
-/
def imageToKernel' (w : f ≫ g = 0) : image f ⟶ kernel g :=
  kernel.lift g (image.ι f)
    (by
      ext
      simpa using w)

@[simp]
theorem image_subobject_iso_image_to_kernel' (w : f ≫ g = 0) :
    (image_subobject_iso f).Hom ≫ imageToKernel' f g w = imageToKernel f g w ≫ (kernel_subobject_iso g).Hom := by
  ext
  simp [imageToKernel']

@[simp]
theorem image_to_kernel'_kernel_subobject_iso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernel_subobject_iso g).inv = (image_subobject_iso f).inv ≫ imageToKernel f g w := by
  ext
  simp [imageToKernel']

variable [has_cokernels V]

/-- 
`homology f g w` can be computed as the cokernel of `image_to_kernel' f g w`.
-/
def homologyIsoCokernelImageToKernel' (w : f ≫ g = 0) : homology f g w ≅ cokernel (imageToKernel' f g w) :=
  { Hom :=
      cokernel.map _ _ (image_subobject_iso f).Hom (kernel_subobject_iso g).Hom
        (by
          simp only [image_subobject_iso_image_to_kernel']),
    inv :=
      cokernel.map _ _ (image_subobject_iso f).inv (kernel_subobject_iso g).inv
        (by
          simp only [image_to_kernel'_kernel_subobject_iso]),
    hom_inv_id' := by
      apply coequalizer.hom_ext
      simp only [iso.hom_inv_id_assoc, cokernel.π_desc, cokernel.π_desc_assoc, category.assoc, coequalizer_as_cokernel]
      exact (category.comp_id _).symm,
    inv_hom_id' := by
      ext1
      simp only [iso.inv_hom_id_assoc, cokernel.π_desc, category.comp_id, cokernel.π_desc_assoc, category.assoc] }

variable [has_equalizers V]

/-- 
`homology f g w` can be computed as the cokernel of `kernel.lift g f w`.
-/
def homologyIsoCokernelLift (w : f ≫ g = 0) : homology f g w ≅ cokernel (kernel.lift g f w) := by
  refine' homologyIsoCokernelImageToKernel' f g w ≪≫ _
  have p : factor_thru_image f ≫ imageToKernel' f g w = kernel.lift g f w := by
    ext
    simp [imageToKernel']
  exact (cokernel_epi_comp _ _).symm ≪≫ cokernel_iso_of_eq p

end imageToKernel'

