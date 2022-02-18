import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminal_comparison G` is an isomorphism iff `G` preserves terminal
objects.
-/


universe v v₁ v₂ u u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable (X : C)

section Terminal

/-- The map of an empty cone is a limit iff the mapped object is terminal.
-/
def is_limit_map_cone_empty_cone_equiv : IsLimit (G.mapCone (asEmptyCone.{v₁} X)) ≃ IsTerminal (G.obj X) :=
  isLimitEmptyConeEquiv D _ _ (eqToIso rfl)

/-- The property of preserving terminal objects expressed in terms of `is_terminal`. -/
def is_terminal.is_terminal_obj [PreservesLimit (Functor.empty.{v₁} C) G] (l : IsTerminal X) : IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (PreservesLimit.preserves l)

/-- The property of reflecting terminal objects expressed in terms of `is_terminal`. -/
def is_terminal.is_terminal_of_obj [ReflectsLimit (Functor.empty.{v₁} C) G] (l : IsTerminal (G.obj X)) : IsTerminal X :=
  ReflectsLimit.reflects ((isLimitMapConeEmptyConeEquiv G X).symm l)

variable [HasTerminal C]

/-- If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def is_limit_of_has_terminal_of_preserves_limit [PreservesLimit (Functor.empty.{v₁} C) G] : IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)

/-- If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
theorem has_terminal_of_has_terminal_of_preserves_limit [PreservesLimit (Functor.empty.{v₁} C) G] : HasTerminal D :=
  ⟨fun F => by
    have := has_limit.mk ⟨_, is_limit_of_has_terminal_of_preserves_limit G⟩
    apply has_limit_of_iso F.unique_from_empty.symm⟩

variable [HasTerminal D]

/-- If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def preserves_terminal.of_iso_comparison [i : IsIso (terminalComparison G)] : PreservesLimit (Functor.empty C) G := by
  apply preserves_limit_of_preserves_limit_cone terminal_is_terminal
  apply (is_limit_map_cone_empty_cone_equiv _ _).symm _
  apply is_limit.of_point_iso (limit.is_limit (Functor.empty.{v₂} D))
  apply i

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_is_iso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] : PreservesLimit (Functor.empty C) G := by
  rw [Subsingleton.elimₓ f (terminal_comparison G)] at i
  exact preserves_terminal.of_iso_comparison G

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
def preserves_terminal_of_iso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty C) G :=
  preservesTerminalOfIsIso G f.Hom

variable [PreservesLimit (Functor.empty.{v₁} C) G]

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` is an isomorphism.
-/
def preserves_terminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)

@[simp]
theorem preserves_terminal.iso_hom : (PreservesTerminal.iso G).Hom = terminalComparison G :=
  rfl

instance : IsIso (terminalComparison G) := by
  rw [← preserves_terminal.iso_hom]
  infer_instance

end Terminal

section Initial

/-- The map of an empty cocone is a colimit iff the mapped object is initial.
-/
def is_colimit_map_cocone_empty_cocone_equiv : IsColimit (G.mapCocone (asEmptyCocone.{v₁} X)) ≃ IsInitial (G.obj X) :=
  isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)

/-- The property of preserving initial objects expressed in terms of `is_initial`. -/
def is_initial.is_initial_obj [PreservesColimit (Functor.empty.{v₁} C) G] (l : IsInitial X) : IsInitial (G.obj X) :=
  isColimitMapCoconeEmptyCoconeEquiv G X (PreservesColimit.preserves l)

/-- The property of reflecting initial objects expressed in terms of `is_initial`. -/
def is_initial.is_initial_of_obj [ReflectsColimit (Functor.empty.{v₁} C) G] (l : IsInitial (G.obj X)) : IsInitial X :=
  ReflectsColimit.reflects ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)

variable [HasInitial C]

/-- If `G` preserves the initial object and `C` has a initial object, then the image of the initial
object is initial.
-/
def is_colimit_of_has_initial_of_preserves_colimit [PreservesColimit (Functor.empty.{v₁} C) G] :
    IsInitial (G.obj (⊥_ C)) :=
  initialIsInitial.isInitialObj G (⊥_ C)

/-- If `C` has a initial object and `G` preserves initial objects, then `D` has a initial object
also.
Note this property is somewhat unique to colimits of the empty diagram: for general `J`, if `C`
has colimits of shape `J` and `G` preserves them, then `D` does not necessarily have colimits of
shape `J`.
-/
theorem has_initial_of_has_initial_of_preserves_colimit [PreservesColimit (Functor.empty.{v₁} C) G] : HasInitial D :=
  ⟨fun F => by
    have := has_colimit.mk ⟨_, is_colimit_of_has_initial_of_preserves_colimit G⟩
    apply has_colimit_of_iso F.unique_from_empty⟩

variable [HasInitial D]

/-- If the initial comparison map for `G` is an isomorphism, then `G` preserves initial objects.
-/
def preserves_initial.of_iso_comparison [i : IsIso (initialComparison G)] : PreservesColimit (Functor.empty C) G := by
  apply preserves_colimit_of_preserves_colimit_cocone initial_is_initial
  apply (is_colimit_map_cocone_empty_cocone_equiv _ _).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (Functor.empty.{v₂} D))
  apply i

/-- If there is any isomorphism `⊥ ⟶ G.obj ⊥`, then `G` preserves initial objects. -/
def preserves_initial_of_is_iso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] : PreservesColimit (Functor.empty C) G := by
  rw [Subsingleton.elimₓ f (initial_comparison G)] at i
  exact preserves_initial.of_iso_comparison G

/-- If there is any isomorphism `⊥ ≅ G.obj ⊥ `, then `G` preserves initial objects. -/
def preserves_initial_of_iso (f : ⊥_ D ≅ G.obj (⊥_ C)) : PreservesColimit (Functor.empty C) G :=
  preservesInitialOfIsIso G f.Hom

variable [PreservesColimit (Functor.empty.{v₁} C) G]

/-- If `G` preserves initial objects, then the initial comparison map for `G` is an isomorphism. -/
def preserves_initial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
  (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]
theorem preserves_initial.iso_hom : (PreservesInitial.iso G).inv = initialComparison G :=
  rfl

instance : IsIso (initialComparison G) := by
  rw [← preserves_initial.iso_hom]
  infer_instance

end Initial

end CategoryTheory.Limits

