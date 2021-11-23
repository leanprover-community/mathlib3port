import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.CategoryTheory.Limits.Shapes.StrongEpi 
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

We give the constructions
* `split_mono → regular_mono` and
* `regular_mono → mono`
as well as the dual constructions for regular epimorphisms. Additionally, we give the
construction
* `regular_epi ⟶ strong_epi`.

-/


noncomputable theory

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable{C : Type u₁}[category.{v₁} C]

variable{X Y : C}

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class regular_mono(f : X ⟶ Y) where 
  z : C
  (left right : Y ⟶ Z)
  w : f ≫ left = f ≫ right 
  IsLimit : is_limit (fork.of_ι f w)

attribute [reassoc] regular_mono.w

/-- Every regular monomorphism is a monomorphism. -/
instance (priority := 100)regular_mono.mono (f : X ⟶ Y) [regular_mono f] : mono f :=
  mono_of_is_limit_parallel_pair regular_mono.is_limit

instance equalizer_regular (g h : X ⟶ Y) [has_limit (parallel_pair g h)] : regular_mono (equalizer.ι g h) :=
  { z := Y, left := g, right := h, w := equalizer.condition g h,
    IsLimit :=
      fork.is_limit.mk _ (fun s => limit.lift _ s)
        (by 
          simp )
        fun s m w =>
          by 
            ext1 
            simp [←w] }

/-- Every split monomorphism is a regular monomorphism. -/
instance (priority := 100)regular_mono.of_split_mono (f : X ⟶ Y) [split_mono f] : regular_mono f :=
  { z := Y, left := 𝟙 Y, right := retraction f ≫ f,
    w :=
      by 
        tidy,
    IsLimit := split_mono_equalizes f }

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `regular_mono.left` and
    `regular_mono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def regular_mono.lift' {W : C} (f : X ⟶ Y) [regular_mono f] (k : W ⟶ Y)
  (h : k ≫ (regular_mono.left : Y ⟶ @regular_mono.Z _ _ _ _ f _) = k ≫ regular_mono.right) :
  { l : W ⟶ X // l ≫ f = k } :=
  fork.is_limit.lift' regular_mono.is_limit _ h

-- error in CategoryTheory.Limits.Shapes.RegularMono: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_fst_of_regular` for the flipped version.
-/
def regular_of_is_pullback_snd_of_regular
{P Q R S : C}
{f : «expr ⟶ »(P, Q)}
{g : «expr ⟶ »(P, R)}
{h : «expr ⟶ »(Q, S)}
{k : «expr ⟶ »(R, S)}
[hr : regular_mono h]
(comm : «expr = »(«expr ≫ »(f, h), «expr ≫ »(g, k)))
(t : is_limit (pullback_cone.mk _ _ comm)) : regular_mono g :=
{ Z := hr.Z,
  left := «expr ≫ »(k, hr.left),
  right := «expr ≫ »(k, hr.right),
  w := by rw ["[", "<-", expr reassoc_of comm, ",", "<-", expr reassoc_of comm, ",", expr hr.w, "]"] [],
  is_limit := begin
    apply [expr fork.is_limit.mk' _ _],
    intro [ident s],
    have [ident l₁] [":", expr «expr = »(«expr ≫ »(«expr ≫ »(fork.ι s, k), regular_mono.left), «expr ≫ »(«expr ≫ »(fork.ι s, k), regular_mono.right))] [],
    rw ["[", expr category.assoc, ",", expr s.condition, ",", expr category.assoc, "]"] [],
    obtain ["⟨", ident l, ",", ident hl, "⟩", ":=", expr fork.is_limit.lift' hr.is_limit _ l₁],
    obtain ["⟨", ident p, ",", ident hp₁, ",", ident hp₂, "⟩", ":=", expr pullback_cone.is_limit.lift' t _ _ hl],
    refine [expr ⟨p, hp₂, _⟩],
    intros [ident m, ident w],
    have [ident z] [":", expr «expr = »(«expr ≫ »(m, g), «expr ≫ »(p, g))] [":=", expr w.trans hp₂.symm],
    apply [expr t.hom_ext],
    apply [expr (pullback_cone.mk f g comm).equalizer_ext],
    { erw ["[", "<-", expr cancel_mono h, ",", expr category.assoc, ",", expr category.assoc, ",", expr comm, ",", expr reassoc_of z, "]"] [] },
    { exact [expr z] }
  end }

/--
The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_snd_of_regular` for the flipped version.
-/
def regular_of_is_pullback_fst_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hr : regular_mono k] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) : regular_mono f :=
  regular_of_is_pullback_snd_of_regular comm.symm (pullback_cone.flip_is_limit t)

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
theorem is_iso_of_regular_mono_of_epi (f : X ⟶ Y) [regular_mono f] [e : epi f] : is_iso f :=
  @is_iso_limit_cone_parallel_pair_of_epi _ _ _ _ _ _ _ regular_mono.is_limit e

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class regular_epi(f : X ⟶ Y) where 
  w : C
  (left right : W ⟶ X)
  w : left ≫ f = right ≫ f 
  IsColimit : is_colimit (cofork.of_π f w)

attribute [reassoc] regular_epi.w

/-- Every regular epimorphism is an epimorphism. -/
instance (priority := 100)regular_epi.epi (f : X ⟶ Y) [regular_epi f] : epi f :=
  epi_of_is_colimit_parallel_pair regular_epi.is_colimit

instance coequalizer_regular (g h : X ⟶ Y) [has_colimit (parallel_pair g h)] : regular_epi (coequalizer.π g h) :=
  { w := X, left := g, right := h, w := coequalizer.condition g h,
    IsColimit :=
      cofork.is_colimit.mk _ (fun s => colimit.desc _ s)
        (by 
          simp )
        fun s m w =>
          by 
            ext1 
            simp [←w] }

/-- Every split epimorphism is a regular epimorphism. -/
instance (priority := 100)regular_epi.of_split_epi (f : X ⟶ Y) [split_epi f] : regular_epi f :=
  { w := X, left := 𝟙 X, right := f ≫ section_ f,
    w :=
      by 
        tidy,
    IsColimit := split_epi_coequalizes f }

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `regular_epi.left` and
    `regular_epi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def regular_epi.desc' {W : C} (f : X ⟶ Y) [regular_epi f] (k : X ⟶ W)
  (h : (regular_epi.left : regular_epi.W f ⟶ X) ≫ k = regular_epi.right ≫ k) : { l : Y ⟶ W // f ≫ l = k } :=
  cofork.is_colimit.desc' regular_epi.is_colimit _ h

-- error in CategoryTheory.Limits.Shapes.RegularMono: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_fst_of_regular` for the flipped version.
-/
def regular_of_is_pushout_snd_of_regular
{P Q R S : C}
{f : «expr ⟶ »(P, Q)}
{g : «expr ⟶ »(P, R)}
{h : «expr ⟶ »(Q, S)}
{k : «expr ⟶ »(R, S)}
[gr : regular_epi g]
(comm : «expr = »(«expr ≫ »(f, h), «expr ≫ »(g, k)))
(t : is_colimit (pushout_cocone.mk _ _ comm)) : regular_epi h :=
{ W := gr.W,
  left := «expr ≫ »(gr.left, f),
  right := «expr ≫ »(gr.right, f),
  w := by rw ["[", expr category.assoc, ",", expr category.assoc, ",", expr comm, ",", expr reassoc_of gr.w, "]"] [],
  is_colimit := begin
    apply [expr cofork.is_colimit.mk' _ _],
    intro [ident s],
    have [ident l₁] [":", expr «expr = »(«expr ≫ »(gr.left, «expr ≫ »(f, s.π)), «expr ≫ »(gr.right, «expr ≫ »(f, s.π)))] [],
    rw ["[", "<-", expr category.assoc, ",", "<-", expr category.assoc, ",", expr s.condition, "]"] [],
    obtain ["⟨", ident l, ",", ident hl, "⟩", ":=", expr cofork.is_colimit.desc' gr.is_colimit «expr ≫ »(f, cofork.π s) l₁],
    obtain ["⟨", ident p, ",", ident hp₁, ",", ident hp₂, "⟩", ":=", expr pushout_cocone.is_colimit.desc' t _ _ hl.symm],
    refine [expr ⟨p, hp₁, _⟩],
    intros [ident m, ident w],
    have [ident z] [] [":=", expr w.trans hp₁.symm],
    apply [expr t.hom_ext],
    apply [expr (pushout_cocone.mk _ _ comm).coequalizer_ext],
    { exact [expr z] },
    { erw ["[", "<-", expr cancel_epi g, ",", "<-", expr reassoc_of comm, ",", "<-", expr reassoc_of comm, ",", expr z, "]"] [],
      refl }
  end }

/--
The first leg of a pushout cocone is a regular epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_snd_of_regular` for the flipped version.
-/
def regular_of_is_pushout_fst_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [fr : regular_epi f] (comm : f ≫ h = g ≫ k) (t : is_colimit (pushout_cocone.mk _ _ comm)) : regular_epi k :=
  regular_of_is_pushout_snd_of_regular comm.symm (pushout_cocone.flip_is_colimit t)

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
theorem is_iso_of_regular_epi_of_mono (f : X ⟶ Y) [regular_epi f] [m : mono f] : is_iso f :=
  @is_iso_limit_cocone_parallel_pair_of_epi _ _ _ _ _ _ _ regular_epi.is_colimit m

-- error in CategoryTheory.Limits.Shapes.RegularMono: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance strong_epi_of_regular_epi (f : «expr ⟶ »(X, Y)) [regular_epi f] : strong_epi f :=
{ epi := by apply_instance,
  has_lift := begin
    introsI [],
    have [] [":", expr «expr = »(«expr ≫ »((regular_epi.left : «expr ⟶ »(regular_epi.W f, X)), u), «expr ≫ »(regular_epi.right, u))] [],
    { apply [expr (cancel_mono z).1],
      simp [] [] ["only"] ["[", expr category.assoc, ",", expr h, ",", expr regular_epi.w_assoc, "]"] [] [] },
    obtain ["⟨", ident t, ",", ident ht, "⟩", ":=", expr regular_epi.desc' f u this],
    exact [expr arrow.has_lift.mk ⟨t, ht, (cancel_epi f).1 (by simp [] [] ["only"] ["[", "<-", expr category.assoc, ",", expr ht, ",", "<-", expr h, ",", expr arrow.mk_hom, ",", expr arrow.hom_mk'_right, "]"] [] [])⟩]
  end }

end CategoryTheory

