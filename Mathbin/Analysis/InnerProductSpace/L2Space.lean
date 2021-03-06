/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.NormedSpace.LpSpace

/-!
# Hilbert sum of a family of inner product spaces

Given a family `(G : ฮน โ Type*) [ฮ  i, inner_product_space ๐ (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : ฮ  i, G i` for which `โ' i, โฅf iโฅ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the *Hilbert sum* of the family `G`.  By choosing
`G` to be `ฮน โ ๐`, the Hilbert space `โยฒ(ฮน, ๐)` may be seen as a special case of this construction.

## Main definitions

* `orthogonal_family.linear_isometry`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : ฮ  i, G i โโแตข[๐] E` of isometric embeddings of the `G i` into `E` with
  mutually-orthogonal images, there is an induced isometric embedding of the Hilbert sum of `G`
  into `E`.

* `orthogonal_family.linear_isometry_equiv`: Given a Hilbert space `E`, a family `G` of inner
  product spaces and a family `V : ฮ  i, G i โโแตข[๐] E` of isometric embeddings of the `G i` into `E`
  with mutually-orthogonal images whose span is dense in `E`, there is an induced isometric
  isomorphism of the Hilbert sum of `G` with `E`.

* `hilbert_basis`: We define a *Hilbert basis* of a Hilbert space `E` to be a structure whose single
  field `hilbert_basis.repr` is an isometric isomorphism of `E` with `โยฒ(ฮน, ๐)` (i.e., the Hilbert
  sum of `ฮน` copies of `๐`).  This parallels the definition of `basis`, in `linear_algebra.basis`,
  as an isomorphism of an `R`-module with `ฮน โโ R`.

* `hilbert_basis.has_coe_to_fun`: More conventionally a Hilbert basis is thought of as a family
  `ฮน โ E` of vectors in `E` satisfying certain properties (orthonormality, completeness).  We obtain
  this interpretation of a Hilbert basis `b` by defining `โb`, of type `ฮน โ E`, to be the image
  under `b.repr` of `lp.single 2 i (1:๐)`.  This parallels the definition `basis.has_coe_to_fun` in
  `linear_algebra.basis`.

* `hilbert_basis.mk`: Make a Hilbert basis of `E` from an orthonormal family `v : ฮน โ E` of vectors
  in `E` whose span is dense.  This parallels the definition `basis.mk` in `linear_algebra.basis`.

* `hilbert_basis.mk_of_orthogonal_eq_bot`: Make a Hilbert basis of `E` from an orthonormal family
  `v : ฮน โ E` of vectors in `E` whose span has trivial orthogonal complement.

## Main results

* `lp.inner_product_space`: Construction of the inner product space instance on the Hilbert sum
  `lp G 2`.  Note that from the file `analysis.normed_space.lp_space`, the space `lp G 2` already
  held a normed space instance (`lp.normed_space`), and if each `G i` is a Hilbert space (i.e.,
  complete), then `lp G 2` was already known to be complete (`lp.complete_space`).  So the work
  here is to define the inner product and show it is compatible.

* `orthogonal_family.range_linear_isometry`: Given a family `G` of inner product spaces and a family
  `V : ฮ  i, G i โโแตข[๐] E` of isometric embeddings of the `G i` into `E` with mutually-orthogonal
  images, the image of the embedding `orthogonal_family.linear_isometry` of the Hilbert sum of `G`
  into `E` is the closure of the span of the images of the `G i`.

* `hilbert_basis.repr_apply_apply`: Given a Hilbert basis `b` of `E`, the entry `b.repr x i` of
  `x`'s representation in `โยฒ(ฮน, ๐)` is the inner product `โชb i, xโซ`.

* `hilbert_basis.has_sum_repr`: Given a Hilbert basis `b` of `E`, a vector `x` in `E` can be
  expressed as the "infinite linear combination" `โ' i, b.repr x i โข b i` of the basis vectors
  `b i`, with coefficients given by the entries `b.repr x i` of `x`'s representation in `โยฒ(ฮน, ๐)`.

* `exists_hilbert_basis`: A Hilbert space admits a Hilbert basis.

## Keywords

Hilbert space, Hilbert sum, l2, Hilbert basis, unitary equivalence, isometric isomorphism
-/


open IsROrC Submodule Filter

open BigOperators Nnreal Ennreal Classical ComplexConjugate

noncomputable section

variable {ฮน : Type _}

variable {๐ : Type _} [IsROrC ๐] {E : Type _} [InnerProductSpace ๐ E] [cplt : CompleteSpace E]

variable {G : ฮน โ Type _} [โ i, InnerProductSpace ๐ (G i)]

-- mathport name: ยซexprโช , โซยป
local notation "โช" x ", " y "โซ" => @inner ๐ _ _ x y

-- mathport name: ยซexprโยฒ( , )ยป
notation "โยฒ(" ฮน "," ๐ ")" => lp (fun i : ฮน => ๐) 2

/-! ### Inner product space structure on `lp G 2` -/


namespace lp

theorem summable_inner (f g : lp G 2) : Summable fun i => โชf i, g iโซ := by
  -- Apply the Direct Comparison Test, comparing with โ' i, โฅf iโฅ * โฅg iโฅ (summable by Hรถlder)
  refine' summable_of_norm_bounded (fun i => โฅf iโฅ * โฅg iโฅ) (lp.summable_mul _ f g) _
  ยท rw [Real.is_conjugate_exponent_iff] <;> norm_num
    
  intro i
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm _ _

instance : InnerProductSpace ๐ (lp G 2) :=
  { lp.normedSpace with inner := fun f g => โ' i, โชf i, g iโซ,
    norm_sq_eq_inner := fun f => by
      calc โฅfโฅ ^ 2 = โฅfโฅ ^ (2 : โโฅ0โ).toReal := by
          norm_cast _ = โ' i, โฅf iโฅ ^ (2 : โโฅ0โ).toReal := lp.norm_rpow_eq_tsum _ f _ = โ' i, โฅf iโฅ ^ 2 := by
          norm_cast _ = โ' i, re โชf i, f iโซ := by
          simp only [โ norm_sq_eq_inner]_ = re (โ' i, โชf i, f iโซ) := (is_R_or_C.re_clm.map_tsum _).symm _ = _ := by
          congr
      ยท norm_num
        
      ยท exact summable_inner f f
        ,
    conj_sym := fun f g => by
      calc conj _ = conj (โ' i, โชg i, f iโซ) := by
          congr _ = โ' i, conj โชg i, f iโซ := is_R_or_C.conj_cle.map_tsum _ = โ' i, โชf i, g iโซ := by
          simp only [โ inner_conj_sym]_ = _ := by
          congr,
    add_left := fun fโ fโ g => by
      calc _ = โ' i, โช(fโ + fโ) i, g iโซ := _ _ = โ' i, โชfโ i, g iโซ + โชfโ i, g iโซ := by
          simp only [โ inner_add_left, โ Pi.add_apply, โ coe_fn_add]_ = (โ' i, โชfโ i, g iโซ) + โ' i, โชfโ i, g iโซ :=
          tsum_add _ _ _ = _ := by
          congr
      ยท congr
        
      ยท exact summable_inner fโ g
        
      ยท exact summable_inner fโ g
        ,
    smul_left := fun f g c => by
      calc _ = โ' i, โชc โข f i, g iโซ := _ _ = โ' i, conj c * โชf i, g iโซ := by
          simp only [โ inner_smul_left]_ = conj c * โ' i, โชf i, g iโซ := tsum_mul_left _ = _ := _
      ยท simp only [โ coe_fn_smul, โ Pi.smul_apply]
        
      ยท congr
         }

theorem inner_eq_tsum (f g : lp G 2) : โชf, gโซ = โ' i, โชf i, g iโซ :=
  rfl

theorem has_sum_inner (f g : lp G 2) : HasSum (fun i => โชf i, g iโซ) โชf, gโซ :=
  (summable_inner f g).HasSum

theorem inner_single_left (i : ฮน) (a : G i) (f : lp G 2) : โชlp.single 2 i a, fโซ = โชa, f iโซ := by
  refine' (has_sum_inner (lp.single 2 i a) f).unique _
  convert has_sum_ite_eq i โชa, f iโซ
  ext j
  rw [lp.single_apply]
  split_ifs
  ยท subst h
    
  ยท simp
    

theorem inner_single_right (i : ฮน) (a : G i) (f : lp G 2) : โชf, lp.single 2 i aโซ = โชf i, aโซ := by
  simpa [โ inner_conj_sym] using congr_arg conj (inner_single_left i a f)

end lp

/-! ### Identification of a general Hilbert space `E` with a Hilbert sum -/


namespace OrthogonalFamily

variable {V : โ i, G i โโแตข[๐] E} (hV : OrthogonalFamily ๐ V)

include cplt hV

protected theorem summable_of_lp (f : lp G 2) : Summable fun i => V i (f i) := by
  rw [hV.summable_iff_norm_sq_summable]
  convert (lp.mem_โp f).Summable _
  ยท norm_cast
    
  ยท norm_num
    

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
protected def linearIsometry : lp G 2 โโแตข[๐] E where
  toFun := fun f => โ' i, V i (f i)
  map_add' := fun f g => by
    simp only [โ tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g), โ lp.coe_fn_add, โ Pi.add_apply, โ
      LinearIsometry.map_add]
  map_smul' := fun c f => by
    simpa only [โ LinearIsometry.map_smul, โ Pi.smul_apply, โ lp.coe_fn_smul] using
      tsum_const_smul (hV.summable_of_lp f)
  norm_map' := fun f => by
    classical
    -- needed for lattice instance on `finset ฮน`, for `filter.at_top_ne_bot`
    have H : 0 < (2 : โโฅ0โ).toReal := by
      norm_num
    suffices โฅโ' i : ฮน, V i (f i)โฅ ^ (2 : โโฅ0โ).toReal = โฅfโฅ ^ (2 : โโฅ0โ).toReal by
      exact Real.rpow_left_inj_on H.ne' (norm_nonneg _) (norm_nonneg _) this
    refine' tendsto_nhds_unique _ (lp.has_sum_norm H f)
    convert (hV.summable_of_lp f).HasSum.norm.rpow_const (Or.inr H.le)
    ext s
    exact_mod_cast (hV.norm_sum f s).symm

protected theorem linear_isometry_apply (f : lp G 2) : hV.LinearIsometry f = โ' i, V i (f i) :=
  rfl

protected theorem has_sum_linear_isometry (f : lp G 2) : HasSum (fun i => V i (f i)) (hV.LinearIsometry f) :=
  (hV.summable_of_lp f).HasSum

@[simp]
protected theorem linear_isometry_apply_single {i : ฮน} (x : G i) : hV.LinearIsometry (lp.single 2 i x) = V i x := by
  rw [hV.linear_isometry_apply, โ tsum_ite_eq i (V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs
  ยท subst h
    
  ยท simp
    

@[simp]
protected theorem linear_isometry_apply_dfinsupp_sum_single (Wโ : ฮ โ i : ฮน, G i) :
    hV.LinearIsometry (Wโ.Sum (lp.single 2)) = Wโ.Sum fun i => V i := by
  have :
    hV.linear_isometry (โ i in Wโ.support, lp.single 2 i (Wโ i)) =
      โ i in Wโ.support, hV.linear_isometry (lp.single 2 i (Wโ i)) :=
    hV.linear_isometry.to_linear_map.map_sum
  simp (config := { contextual := true })[โ Dfinsupp.sum, โ this]

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
protected theorem range_linear_isometry [โ i, CompleteSpace (G i)] :
    hV.LinearIsometry.toLinearMap.range = (โจ i, (V i).toLinearMap.range).topologicalClosure := by
  refine' le_antisymmโ _ _
  ยท rintro x โจf, rflโฉ
    refine' mem_closure_of_tendsto (hV.has_sum_linear_isometry f) (eventually_of_forall _)
    intro s
    rw [SetLike.mem_coe]
    refine' sum_mem _
    intro i hi
    refine' mem_supr_of_mem i _
    exact LinearMap.mem_range_self _ (f i)
    
  ยท apply topological_closure_minimal
    ยท refine' supr_le _
      rintro i x โจx, rflโฉ
      use lp.single 2 i x
      exact hV.linear_isometry_apply_single x
      
    exact hV.linear_isometry.isometry.uniform_inducing.is_complete_range.is_closed
    

/-- A mutually orthogonal family of complete subspaces of `E`, whose range is dense in `E`, induces
a isometric isomorphism from E to `lp 2` of the subspaces.

Note that this goes in the opposite direction from `orthogonal_family.linear_isometry`. -/
noncomputable def linearIsometryEquiv [โ i, CompleteSpace (G i)]
    (hV' : (โจ i, (V i).toLinearMap.range).topologicalClosure = โค) : E โโแตข[๐] lp G 2 :=
  LinearIsometryEquiv.symm <|
    LinearIsometryEquiv.ofSurjective hV.LinearIsometry
      (by
        rw [โ LinearIsometry.coe_to_linear_map]
        refine' linear_map.range_eq_top.mp _
        rw [โ hV']
        rw [hV.range_linear_isometry])

/-- In the canonical isometric isomorphism `E โโแตข[๐] lp G 2` induced by an orthogonal family `G`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`. -/
protected theorem linear_isometry_equiv_symm_apply [โ i, CompleteSpace (G i)]
    (hV' : (โจ i, (V i).toLinearMap.range).topologicalClosure = โค) (w : lp G 2) :
    (hV.LinearIsometryEquiv hV').symm w = โ' i, V i (w i) := by
  simp [โ OrthogonalFamily.linearIsometryEquiv, โ OrthogonalFamily.linear_isometry_apply]

/-- In the canonical isometric isomorphism `E โโแตข[๐] lp G 2` induced by an orthogonal family `G`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`, and this
sum indeed converges. -/
protected theorem has_sum_linear_isometry_equiv_symm [โ i, CompleteSpace (G i)]
    (hV' : (โจ i, (V i).toLinearMap.range).topologicalClosure = โค) (w : lp G 2) :
    HasSum (fun i => V i (w i)) ((hV.LinearIsometryEquiv hV').symm w) := by
  simp [โ OrthogonalFamily.linearIsometryEquiv, โ OrthogonalFamily.has_sum_linear_isometry]

/-- In the canonical isometric isomorphism `E โโแตข[๐] lp G 2` induced by an `ฮน`-indexed orthogonal
family `G`, an "elementary basis vector" in `lp G 2` supported at `i : ฮน` is the image of the
associated element in `E`. -/
@[simp]
protected theorem linear_isometry_equiv_symm_apply_single [โ i, CompleteSpace (G i)]
    (hV' : (โจ i, (V i).toLinearMap.range).topologicalClosure = โค) {i : ฮน} (x : G i) :
    (hV.LinearIsometryEquiv hV').symm (lp.single 2 i x) = V i x := by
  simp [โ OrthogonalFamily.linearIsometryEquiv, โ OrthogonalFamily.linear_isometry_apply_single]

/-- In the canonical isometric isomorphism `E โโแตข[๐] lp G 2` induced by an `ฮน`-indexed orthogonal
family `G`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp]
protected theorem linear_isometry_equiv_symm_apply_dfinsupp_sum_single [โ i, CompleteSpace (G i)]
    (hV' : (โจ i, (V i).toLinearMap.range).topologicalClosure = โค) (Wโ : ฮ โ i : ฮน, G i) :
    (hV.LinearIsometryEquiv hV').symm (Wโ.Sum (lp.single 2)) = Wโ.Sum fun i => V i := by
  simp [โ OrthogonalFamily.linearIsometryEquiv, โ OrthogonalFamily.linear_isometry_apply_dfinsupp_sum_single]

/-- In the canonical isometric isomorphism `E โโแตข[๐] lp G 2` induced by an `ฮน`-indexed orthogonal
family `G`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp]
protected theorem linear_isometry_equiv_apply_dfinsupp_sum_single [โ i, CompleteSpace (G i)]
    (hV' : (โจ i, (V i).toLinearMap.range).topologicalClosure = โค) (Wโ : ฮ โ i : ฮน, G i) :
    (hV.LinearIsometryEquiv hV' (Wโ.Sum fun i => V i) : โ i, G i) = Wโ := by
  rw [โ hV.linear_isometry_equiv_symm_apply_dfinsupp_sum_single hV']
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp (config := { contextual := true })[โ Dfinsupp.sum, โ lp.single_apply]

end OrthogonalFamily

/-! ### Hilbert bases -/


section

variable (ฮน) (๐) (E)

/-- A Hilbert basis on `ฮน` for an inner product space `E` is an identification of `E` with the `lp`
space `โยฒ(ฮน, ๐)`. -/
structure HilbertBasis where of_repr ::
  repr : E โโแตข[๐] โยฒ(ฮน,๐)

end

namespace HilbertBasis

instance {ฮน : Type _} : Inhabited (HilbertBasis ฮน ๐ โยฒ(ฮน,๐)) :=
  โจof_repr (LinearIsometryEquiv.refl ๐ _)โฉ

/-- `b i` is the `i`th basis vector. -/
instance : CoeFun (HilbertBasis ฮน ๐ E) fun _ => ฮน โ E where coe := fun b i => b.repr.symm (lp.single 2 i (1 : ๐))

@[simp]
protected theorem repr_symm_single (b : HilbertBasis ฮน ๐ E) (i : ฮน) : b.repr.symm (lp.single 2 i (1 : ๐)) = b i :=
  rfl

@[simp]
protected theorem repr_self (b : HilbertBasis ฮน ๐ E) (i : ฮน) : b.repr (b i) = lp.single 2 i (1 : ๐) := by
  rw [โ b.repr_symm_single, LinearIsometryEquiv.apply_symm_apply]

protected theorem repr_apply_apply (b : HilbertBasis ฮน ๐ E) (v : E) (i : ฮน) : b.repr v i = โชb i, vโซ := by
  rw [โ b.repr.inner_map_map (b i) v, b.repr_self, lp.inner_single_left]
  simp

@[simp]
protected theorem orthonormal (b : HilbertBasis ฮน ๐ E) : Orthonormal ๐ b := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [โ b.repr.inner_map_map (b i) (b j), b.repr_self, b.repr_self, lp.inner_single_left, lp.single_apply]
  simp

protected theorem has_sum_repr_symm (b : HilbertBasis ฮน ๐ E) (f : โยฒ(ฮน,๐)) :
    HasSum (fun i => f i โข b i) (b.repr.symm f) := by
  suffices H :
    (fun i : ฮน => f i โข b i) = fun b_1 : ฮน =>
      b.repr.symm.to_continuous_linear_equiv ((fun i : ฮน => lp.single 2 i (f i)) b_1)
  ยท rw [H]
    have : HasSum (fun i : ฮน => lp.single 2 i (f i)) f := lp.has_sum_single Ennreal.two_ne_top f
    exact (โb.repr.symm.to_continuous_linear_equiv : โยฒ(ฮน,๐) โL[๐] E).HasSum this
    
  ext i
  apply b.repr.injective
  have : lp.single 2 i (f i * 1) = f i โข lp.single 2 i 1 := lp.single_smul 2 i (1 : ๐) (f i)
  rw [mul_oneโ] at this
  rw [LinearIsometryEquiv.map_smul, b.repr_self, โ this, LinearIsometryEquiv.coe_to_continuous_linear_equiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm

protected theorem has_sum_repr (b : HilbertBasis ฮน ๐ E) (x : E) : HasSum (fun i => b.repr x i โข b i) x := by
  simpa using b.has_sum_repr_symm (b.repr x)

@[simp]
protected theorem dense_span (b : HilbertBasis ฮน ๐ E) : (span ๐ (Set.Range b)).topologicalClosure = โค := by
  classical
  rw [eq_top_iff]
  rintro x -
  refine' mem_closure_of_tendsto (b.has_sum_repr x) (eventually_of_forall _)
  intro s
  simp only [โ SetLike.mem_coe]
  refine' sum_mem _
  rintro i -
  refine' smul_mem _ _ _
  exact subset_span โจi, rflโฉ

variable {v : ฮน โ E} (hv : Orthonormal ๐ v)

include hv cplt

/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
protected def mk (hsp : (span ๐ (Set.Range v)).topologicalClosure = โค) : HilbertBasis ฮน ๐ E :=
  HilbertBasis.of_repr <|
    hv.OrthogonalFamily.LinearIsometryEquiv
      (by
        convert hsp
        simp [LinearMap.span_singleton_eq_range, Submodule.span_Union])

theorem _root_.orthonormal.linear_isometry_equiv_symm_apply_single_one (h i) :
    (hv.OrthogonalFamily.LinearIsometryEquiv h).symm (lp.single 2 i 1) = v i := by
  rw [OrthogonalFamily.linear_isometry_equiv_symm_apply_single, LinearIsometry.to_span_singleton_apply, one_smul]

@[simp]
protected theorem coe_mk (hsp : (span ๐ (Set.Range v)).topologicalClosure = โค) : โ(HilbertBasis.mk hv hsp) = v :=
  funext <| Orthonormal.linear_isometry_equiv_symm_apply_single_one hv _

/-- An orthonormal family of vectors whose span has trivial orthogonal complement is a Hilbert
basis. -/
protected def mkOfOrthogonalEqBot (hsp : (span ๐ (Set.Range v))แฎ = โฅ) : HilbertBasis ฮน ๐ E :=
  HilbertBasis.mk hv
    (by
      rw [โ orthogonal_orthogonal_eq_closure, orthogonal_eq_top_iff, hsp])

@[simp]
protected theorem coe_of_orthogonal_eq_bot_mk (hsp : (span ๐ (Set.Range v))แฎ = โฅ) :
    โ(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v :=
  HilbertBasis.coe_mk hv _

omit hv

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
theorem _root_.orthonormal.exists_hilbert_basis_extension {s : Set E} (hs : Orthonormal ๐ (coe : s โ E)) :
    โ (w : Set E)(b : HilbertBasis w ๐ E), s โ w โง โb = (coe : w โ E) :=
  let โจw, hws, hw_ortho, hw_maxโฉ := exists_maximal_orthonormal hs
  โจw,
    HilbertBasis.mkOfOrthogonalEqBot hw_ortho
      (by
        simpa [โ maximal_orthonormal_iff_orthogonal_complement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_of_orthogonal_eq_bot_mk _ _โฉ

variable (๐ E)

/-- A Hilbert space admits a Hilbert basis. -/
theorem _root_.exists_hilbert_basis : โ (w : Set E)(b : HilbertBasis w ๐ E), โb = (coe : w โ E) :=
  let โจw, hw, hw', hw''โฉ := (orthonormal_empty ๐ E).exists_hilbert_basis_extension
  โจw, hw, hw''โฉ

end HilbertBasis

