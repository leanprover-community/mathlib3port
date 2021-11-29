import Mathbin.FieldTheory.Adjoin 
import Mathbin.FieldTheory.Tower 
import Mathbin.GroupTheory.Solvable 
import Mathbin.RingTheory.PowerBasis

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (`normal.of_is_splitting_field` and
`normal.exists_is_splitting_field`).

## Main Definitions

- `normal F K` where `K` is a field extension of `F`.
-/


noncomputable theory

open_locale BigOperators

open_locale Classical

open Polynomial IsScalarTower

variable(F K : Type _)[Field F][Field K][Algebra F K]

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
class Normal : Prop where 
  is_integral' (x : K) : IsIntegral F x 
  splits' (x : K) : splits (algebraMap F K) (minpoly F x)

variable{F K}

theorem Normal.is_integral (h : Normal F K) (x : K) : IsIntegral F x :=
  Normal.is_integral' x

theorem Normal.splits (h : Normal F K) (x : K) : splits (algebraMap F K) (minpoly F x) :=
  Normal.splits' x

theorem normal_iff : Normal F K ↔ ∀ (x : K), IsIntegral F x ∧ splits (algebraMap F K) (minpoly F x) :=
  ⟨fun h x => ⟨h.is_integral x, h.splits x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

theorem Normal.out : Normal F K → ∀ (x : K), IsIntegral F x ∧ splits (algebraMap F K) (minpoly F x) :=
  normal_iff.1

variable(F K)

instance normal_self : Normal F F :=
  ⟨fun x => is_integral_algebra_map,
    fun x =>
      by 
        rw [minpoly.eq_X_sub_C']
        exact splits_X_sub_C _⟩

variable{K}

variable(K)

theorem Normal.exists_is_splitting_field [h : Normal F K] [FiniteDimensional F K] :
  ∃ p : Polynomial F, is_splitting_field F K p :=
  by 
    let s := Basis.ofVectorSpace F K 
    refine' ⟨∏x, minpoly F (s x), splits_prod _$ fun x hx => h.splits (s x), Subalgebra.to_submodule_injective _⟩
    rw [Algebra.top_to_submodule, eq_top_iff, ←s.span_eq, Submodule.span_le, Set.range_subset_iff]
    refine'
      fun x =>
        Algebra.subset_adjoin
          (multiset.mem_to_finset.mpr$
            (mem_roots$ mt (map_eq_zero$ algebraMap F K).1$ Finset.prod_ne_zero_iff.2$ fun x hx => _).2 _)
    ·
      exact minpoly.ne_zero (h.is_integral (s x))
    rw [is_root.def, eval_map, ←aeval_def, AlgHom.map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ _) (minpoly.aeval _ _)

section NormalTower

variable(E : Type _)[Field E][Algebra F E][Algebra K E][IsScalarTower F K E]

theorem Normal.tower_top_of_normal [h : Normal F E] : Normal K E :=
  normal_iff.2$
    fun x =>
      by 
        cases' h.out x with hx hhx 
        rw [algebra_map_eq F K E] at hhx 
        exact
          ⟨is_integral_of_is_scalar_tower x hx,
            Polynomial.splits_of_splits_of_dvd (algebraMap K E) (Polynomial.map_ne_zero (minpoly.ne_zero hx))
              ((Polynomial.splits_map_iff (algebraMap F K) (algebraMap K E)).mpr hhx)
              (minpoly.dvd_map_of_is_scalar_tower F K x)⟩

-- error in FieldTheory.Normal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem alg_hom.normal_bijective [h : normal F E] (ϕ : «expr →ₐ[ ] »(E, F, K)) : function.bijective ϕ :=
⟨ϕ.to_ring_hom.injective, λ x, by { letI [] [":", expr algebra E K] [":=", expr ϕ.to_ring_hom.to_algebra],
   obtain ["⟨", ident h1, ",", ident h2, "⟩", ":=", expr h.out (algebra_map K E x)],
   cases [expr minpoly.mem_range_of_degree_eq_one E x (or.resolve_left h2 (minpoly.ne_zero h1) (minpoly.irreducible (is_integral_of_is_scalar_tower x ((is_integral_algebra_map_iff (algebra_map K E).injective).mp h1))) (minpoly.dvd E x ((algebra_map K E).injective (by { rw ["[", expr ring_hom.map_zero, ",", expr aeval_map, ",", "<-", expr is_scalar_tower.to_alg_hom_apply F K E, ",", "<-", expr alg_hom.comp_apply, ",", "<-", expr aeval_alg_hom, "]"] [],
          exact [expr minpoly.aeval F (algebra_map K E x)] }))))] ["with", ident y, ident hy],
   exact [expr ⟨y, hy⟩] }⟩

variable{F}{E}{E' : Type _}[Field E'][Algebra F E']

-- error in FieldTheory.Normal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normal.of_alg_equiv [h : normal F E] (f : «expr ≃ₐ[ ] »(E, F, E')) : normal F E' :=
«expr $ »(normal_iff.2, λ x, begin
   cases [expr h.out (f.symm x)] ["with", ident hx, ident hhx],
   have [ident H] [] [":=", expr is_integral_alg_hom f.to_alg_hom hx],
   rw ["[", expr alg_equiv.to_alg_hom_eq_coe, ",", expr alg_equiv.coe_alg_hom, ",", expr alg_equiv.apply_symm_apply, "]"] ["at", ident H],
   use [expr H],
   apply [expr polynomial.splits_of_splits_of_dvd (algebra_map F E') (minpoly.ne_zero hx)],
   { rw ["<-", expr alg_hom.comp_algebra_map f.to_alg_hom] [],
     exact [expr polynomial.splits_comp_of_splits (algebra_map F E) f.to_alg_hom.to_ring_hom hhx] },
   { apply [expr minpoly.dvd _ _],
     rw ["<-", expr add_equiv.map_eq_zero_iff f.symm.to_add_equiv] [],
     exact [expr eq.trans (polynomial.aeval_alg_hom_apply f.symm.to_alg_hom x (minpoly F (f.symm x))).symm (minpoly.aeval _ _)] }
 end)

theorem AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E' :=
  ⟨fun h =>
      by 
        exact Normal.of_alg_equiv f,
    fun h =>
      by 
        exact Normal.of_alg_equiv f.symm⟩

-- error in FieldTheory.Normal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normal.of_is_splitting_field (p : polynomial F) [hFEp : is_splitting_field F E p] : normal F E :=
begin
  by_cases [expr hp, ":", expr «expr = »(p, 0)],
  { haveI [] [":", expr is_splitting_field F F p] [],
    { rw [expr hp] [],
      exact [expr ⟨splits_zero _, subsingleton.elim _ _⟩] },
    exactI [expr (alg_equiv.transfer_normal ((is_splitting_field.alg_equiv F p).trans (is_splitting_field.alg_equiv E p).symm)).mp (normal_self F)] },
  refine [expr normal_iff.2 (λ x, _)],
  haveI [ident hFE] [":", expr finite_dimensional F E] [":=", expr is_splitting_field.finite_dimensional E p],
  have [ident Hx] [":", expr is_integral F x] [":=", expr is_integral_of_noetherian (is_noetherian.iff_fg.2 hFE) x],
  refine [expr ⟨Hx, or.inr _⟩],
  rintros [ident q, ident q_irred, "⟨", ident r, ",", ident hr, "⟩"],
  let [ident D] [] [":=", expr adjoin_root q],
  let [ident pbED] [] [":=", expr adjoin_root.power_basis q_irred.ne_zero],
  haveI [] [":", expr finite_dimensional E D] [":=", expr power_basis.finite_dimensional pbED],
  have [ident finrankED] [":", expr «expr = »(finite_dimensional.finrank E D, q.nat_degree)] [":=", expr power_basis.finrank pbED],
  letI [] [":", expr algebra F D] [":=", expr ring_hom.to_algebra ((algebra_map E D).comp (algebra_map F E))],
  haveI [] [":", expr is_scalar_tower F E D] [":=", expr of_algebra_map_eq (λ _, rfl)],
  haveI [] [":", expr finite_dimensional F D] [":=", expr finite_dimensional.trans F E D],
  suffices [] [":", expr nonempty «expr →ₐ[ ] »(D, F, E)],
  { cases [expr this] ["with", ident ϕ],
    rw ["[", "<-", expr with_bot.coe_one, ",", expr degree_eq_iff_nat_degree_eq q_irred.ne_zero, ",", "<-", expr finrankED, "]"] [],
    have [ident nat_lemma] [":", expr ∀
     a b c : exprℕ(), «expr = »(«expr * »(a, b), c) → «expr ≤ »(c, a) → «expr < »(0, c) → «expr = »(b, 1)] [],
    { intros [ident a, ident b, ident c, ident h1, ident h2, ident h3],
      nlinarith [] [] [] },
    exact [expr nat_lemma _ _ _ (finite_dimensional.finrank_mul_finrank F E D) (linear_map.finrank_le_finrank_of_injective (show function.injective ϕ.to_linear_map, from ϕ.to_ring_hom.injective)) finite_dimensional.finrank_pos] },
  let [ident C] [] [":=", expr adjoin_root (minpoly F x)],
  have [ident Hx_irred] [] [":=", expr minpoly.irreducible Hx],
  letI [] [":", expr algebra C D] [":=", expr ring_hom.to_algebra (adjoin_root.lift (algebra_map F D) (adjoin_root.root q) (by rw ["[", expr algebra_map_eq F E D, ",", "<-", expr eval₂_map, ",", expr hr, ",", expr adjoin_root.algebra_map_eq, ",", expr eval₂_mul, ",", expr adjoin_root.eval₂_root, ",", expr zero_mul, "]"] []))],
  letI [] [":", expr algebra C E] [":=", expr ring_hom.to_algebra (adjoin_root.lift (algebra_map F E) x (minpoly.aeval F x))],
  haveI [] [":", expr is_scalar_tower F C D] [":=", expr of_algebra_map_eq (λ x, (adjoin_root.lift_of _).symm)],
  haveI [] [":", expr is_scalar_tower F C E] [":=", expr of_algebra_map_eq (λ x, (adjoin_root.lift_of _).symm)],
  suffices [] [":", expr nonempty «expr →ₐ[ ] »(D, C, E)],
  { exact [expr nonempty.map (alg_hom.restrict_scalars F) this] },
  let [ident S] [":", expr set D] [":=", expr ((p.map (algebra_map F E)).roots.map (algebra_map E D)).to_finset],
  suffices [] [":", expr «expr ≤ »(«expr⊤»(), intermediate_field.adjoin C S)],
  { refine [expr intermediate_field.alg_hom_mk_adjoin_splits' (top_le_iff.mp this) (λ y hy, _)],
    rcases [expr multiset.mem_map.mp (multiset.mem_to_finset.mp hy), "with", "⟨", ident z, ",", ident hz1, ",", ident hz2, "⟩"],
    have [ident Hz] [":", expr is_integral F z] [":=", expr is_integral_of_noetherian (is_noetherian.iff_fg.2 hFE) z],
    use [expr show is_integral C y, from is_integral_of_noetherian (is_noetherian.iff_fg.2 (finite_dimensional.right F C D)) y],
    apply [expr splits_of_splits_of_dvd (algebra_map C E) (map_ne_zero (minpoly.ne_zero Hz))],
    { rw ["[", expr splits_map_iff, ",", "<-", expr algebra_map_eq F C E, "]"] [],
      exact [expr splits_of_splits_of_dvd _ hp hFEp.splits (minpoly.dvd F z (eq.trans (eval₂_eq_eval_map _) ((mem_roots (map_ne_zero hp)).mp hz1)))] },
    { apply [expr minpoly.dvd],
      rw ["[", "<-", expr hz2, ",", expr aeval_def, ",", expr eval₂_map, ",", "<-", expr algebra_map_eq F C D, ",", expr algebra_map_eq F E D, ",", "<-", expr hom_eval₂, ",", "<-", expr aeval_def, ",", expr minpoly.aeval F z, ",", expr ring_hom.map_zero, "]"] [] } },
  rw ["[", "<-", expr intermediate_field.to_subalgebra_le_to_subalgebra, ",", expr intermediate_field.top_to_subalgebra, "]"] [],
  apply [expr ge_trans (intermediate_field.algebra_adjoin_le_adjoin C S)],
  suffices [] [":", expr «expr = »((algebra.adjoin C S).restrict_scalars F, (algebra.adjoin E {adjoin_root.root q}).restrict_scalars F)],
  { rw ["[", expr adjoin_root.adjoin_root_eq_top, ",", expr subalgebra.restrict_scalars_top, ",", "<-", expr @subalgebra.restrict_scalars_top F C, "]"] ["at", ident this],
    exact [expr top_le_iff.mpr (subalgebra.restrict_scalars_injective F this)] },
  dsimp ["only"] ["[", expr S, "]"] [] [],
  rw ["[", "<-", expr finset.image_to_finset, ",", expr finset.coe_image, "]"] [],
  apply [expr eq.trans (algebra.adjoin_res_eq_adjoin_res F E C D hFEp.adjoin_roots adjoin_root.adjoin_root_eq_top)],
  rw ["[", expr set.image_singleton, ",", expr ring_hom.algebra_map_to_algebra, ",", expr adjoin_root.lift_root, "]"] []
end

instance  (p : Polynomial F) : Normal F p.splitting_field :=
  Normal.of_is_splitting_field p

end NormalTower

variable{F}{K}(ϕ ψ : K →ₐ[F] K)(χ ω : K ≃ₐ[F] K)

section Restrict

variable(E : Type _)[Field E][Algebra F E][Algebra E K][IsScalarTower F E K]

/-- Restrict algebra homomorphism to image of normal subfield -/
def AlgHom.restrictNormalAux [h : Normal F E] : (to_alg_hom F E K).range →ₐ[F] (to_alg_hom F E K).range :=
  { toFun :=
      fun x =>
        ⟨ϕ x,
          by 
            suffices  : (to_alg_hom F E K).range.map ϕ ≤ _
            ·
              exact this ⟨x, Subtype.mem x, rfl⟩
            rintro x ⟨y, ⟨z, hy⟩, hx⟩
            rw [←hx, ←hy]
            apply minpoly.mem_range_of_degree_eq_one E 
            exact
              Or.resolve_left (h.splits z) (minpoly.ne_zero (h.is_integral z))
                (minpoly.irreducible$
                  is_integral_of_is_scalar_tower _$ is_integral_alg_hom ϕ$ is_integral_alg_hom _$ h.is_integral z)
                (minpoly.dvd E _$
                  by 
                    rw [aeval_map, aeval_alg_hom, aeval_alg_hom, AlgHom.comp_apply, AlgHom.comp_apply, minpoly.aeval,
                      AlgHom.map_zero, AlgHom.map_zero])⟩,
    map_zero' := Subtype.ext ϕ.map_zero, map_one' := Subtype.ext ϕ.map_one,
    map_add' := fun x y => Subtype.ext (ϕ.map_add x y), map_mul' := fun x y => Subtype.ext (ϕ.map_mul x y),
    commutes' := fun x => Subtype.ext (ϕ.commutes x) }

/-- Restrict algebra homomorphism to normal subfield -/
def AlgHom.restrictNormal [Normal F E] : E →ₐ[F] E :=
  ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)).symm.toAlgHom.comp (ϕ.restrict_normal_aux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)).toAlgHom

@[simp]
theorem AlgHom.restrict_normal_commutes [Normal F E] (x : E) :
  algebraMap E K (ϕ.restrict_normal E x) = ϕ (algebraMap E K x) :=
  Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K))
      (ϕ.restrict_normal_aux E ⟨IsScalarTower.toAlgHom F E K x, x, rfl⟩))

theorem AlgHom.restrict_normal_comp [Normal F E] :
  (ϕ.restrict_normal E).comp (ψ.restrict_normal E) = (ϕ.comp ψ).restrictNormal E :=
  AlgHom.ext
    fun _ =>
      (algebraMap E K).Injective
        (by 
          simp only [AlgHom.comp_apply, AlgHom.restrict_normal_commutes])

/-- Restrict algebra isomorphism to a normal subfield -/
def AlgEquiv.restrictNormal [h : Normal F E] : E ≃ₐ[F] E :=
  AlgEquiv.ofBijective (χ.to_alg_hom.restrict_normal E) (AlgHom.normal_bijective F E E _)

@[simp]
theorem AlgEquiv.restrict_normal_commutes [Normal F E] (x : E) :
  algebraMap E K (χ.restrict_normal E x) = χ (algebraMap E K x) :=
  χ.to_alg_hom.restrict_normal_commutes E x

theorem AlgEquiv.restrict_normal_trans [Normal F E] :
  (χ.trans ω).restrictNormal E = (χ.restrict_normal E).trans (ω.restrict_normal E) :=
  AlgEquiv.ext
    fun _ =>
      (algebraMap E K).Injective
        (by 
          simp only [AlgEquiv.trans_apply, AlgEquiv.restrict_normal_commutes])

/-- Restriction to an normal subfield as a group homomorphism -/
def AlgEquiv.restrictNormalHom [Normal F E] : (K ≃ₐ[F] K) →* E ≃ₐ[F] E :=
  MonoidHom.mk' (fun χ => χ.restrict_normal E) fun ω χ => χ.restrict_normal_trans ω E

end Restrict

section lift

variable{F}{K}(E : Type _)[Field E][Algebra F E][Algebra K E][IsScalarTower F K E]

/-- If `E/K/F` is a tower of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K →ₐ[F] K` to `ϕ.lift_normal E : E →ₐ[F] E`. -/
noncomputable def AlgHom.liftNormal [h : Normal F E] : E →ₐ[F] E :=
  @AlgHom.restrictScalars F K E E _ _ _ _ _ _ ((IsScalarTower.toAlgHom F K E).comp ϕ).toRingHom.toAlgebra _ _ _ _
    (Nonempty.some
      (@IntermediateField.alg_hom_mk_adjoin_splits' K E E _ _ _ _
        ((IsScalarTower.toAlgHom F K E).comp ϕ).toRingHom.toAlgebra ⊤ rfl
        fun x hx =>
          ⟨is_integral_of_is_scalar_tower x (h.out x).1,
            splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero (h.out x).1))
              (by 
                rw [splits_map_iff, ←IsScalarTower.algebra_map_eq]
                exact (h.out x).2)
              (minpoly.dvd_map_of_is_scalar_tower F K x)⟩))

@[simp]
theorem AlgHom.lift_normal_commutes [Normal F E] (x : K) : ϕ.lift_normal E (algebraMap K E x) = algebraMap K E (ϕ x) :=
  @AlgHom.commutes K E E _ _ _ _ ((IsScalarTower.toAlgHom F K E).comp ϕ).toRingHom.toAlgebra _ x

@[simp]
theorem AlgHom.restrict_lift_normal [Normal F K] [Normal F E] : (ϕ.lift_normal E).restrictNormal K = ϕ :=
  AlgHom.ext
    fun x => (algebraMap K E).Injective (Eq.trans (AlgHom.restrict_normal_commutes _ K x) (ϕ.lift_normal_commutes E x))

/-- If `E/K/F` is a tower of fields with `E/F` normal then we can lift
  an algebra isomorphism `ϕ : K ≃ₐ[F] K` to `ϕ.lift_normal E : E ≃ₐ[F] E`. -/
noncomputable def AlgEquiv.liftNormal [Normal F E] : E ≃ₐ[F] E :=
  AlgEquiv.ofBijective (χ.to_alg_hom.lift_normal E) (AlgHom.normal_bijective F E E _)

@[simp]
theorem AlgEquiv.lift_normal_commutes [Normal F E] (x : K) :
  χ.lift_normal E (algebraMap K E x) = algebraMap K E (χ x) :=
  χ.to_alg_hom.lift_normal_commutes E x

@[simp]
theorem AlgEquiv.restrict_lift_normal [Normal F K] [Normal F E] : (χ.lift_normal E).restrictNormal K = χ :=
  AlgEquiv.ext
    fun x =>
      (algebraMap K E).Injective (Eq.trans (AlgEquiv.restrict_normal_commutes _ K x) (χ.lift_normal_commutes E x))

theorem AlgEquiv.restrict_normal_hom_surjective [Normal F K] [Normal F E] :
  Function.Surjective (AlgEquiv.restrictNormalHom K : (E ≃ₐ[F] E) → K ≃ₐ[F] K) :=
  fun χ => ⟨χ.lift_normal E, χ.restrict_lift_normal E⟩

variable(F)(K)(E)

theorem is_solvable_of_is_scalar_tower [Normal F K] [h1 : IsSolvable (K ≃ₐ[F] K)] [h2 : IsSolvable (E ≃ₐ[K] E)] :
  IsSolvable (E ≃ₐ[F] E) :=
  by 
    let f : (E ≃ₐ[K] E) →* E ≃ₐ[F] E :=
      { toFun :=
          fun ϕ =>
            AlgEquiv.ofAlgHom (ϕ.to_alg_hom.restrict_scalars F) (ϕ.symm.to_alg_hom.restrict_scalars F)
              (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x),
        map_one' := AlgEquiv.ext fun _ => rfl, map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
    refine'
      solvable_of_ker_le_range f (AlgEquiv.restrictNormalHom K)
        fun ϕ hϕ => ⟨{ ϕ with commutes' := fun x => _ }, AlgEquiv.ext fun _ => rfl⟩
    exact Eq.trans (ϕ.restrict_normal_commutes K x).symm (congr_argₓ _ (alg_equiv.ext_iff.mp hϕ x))

end lift

