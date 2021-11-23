import Mathbin.GroupTheory.Coset

/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main definitions

* `mk'`: the canonical group homomorphism `G →* G/N` given a normal subgroup `N` of `G`.
* `lift φ`: the group homomorphism `G/N →* H` given a group homomorphism `φ : G →* H` such that
  `N ⊆ ker φ`.
* `map f`: the group homomorphism `G/N →* H/M` given a group homomorphism `f : G →* H` such that
  `N ⊆ f⁻¹(M)`.

## Main statements

* `quotient_ker_equiv_range`: Noether's first isomorphism theorem, an explicit isomorphism
  `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `quotient_inf_equiv_prod_normal_quotient`: Noether's second isomorphism theorem, an explicit
  isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H` and a normal subgroup `N` of a
  group `G`.
* `quotient_group.quotient_quotient_equiv_quotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / M) / (M / N)` and `G / N`, where `N ≤ M`.

## Tags

isomorphism theorems, quotient groups
-/


universe u v

namespace QuotientGroup

variable{G : Type u}[Groupₓ G](N : Subgroup G)[nN : N.normal]{H : Type v}[Groupₓ H]

include nN

@[toAdditive QuotientAddGroup.divInvMonoid]
instance  : DivInvMonoidₓ (Quotientₓ N) :=
  { one := (1 : G),
    mul :=
      Quotientₓ.map₂' (·*·)
        fun a₁ b₁ hab₁ a₂ b₂ hab₂ =>
          (N.mul_mem_cancel_right (N.inv_mem hab₂)).1
            (by 
              rw [mul_inv_rev, mul_inv_rev, ←mul_assocₓ (a₂⁻¹*a₁⁻¹), mul_assocₓ _ b₂, ←mul_assocₓ b₂, mul_inv_selfₓ,
                  one_mulₓ, mul_assocₓ (a₂⁻¹)] <;>
                exact nN.conj_mem _ hab₁ _),
    mul_assoc := fun a b c => Quotientₓ.induction_on₃' a b c fun a b c => congr_argₓ mk (mul_assocₓ a b c),
    one_mul := fun a => Quotientₓ.induction_on' a fun a => congr_argₓ mk (one_mulₓ a),
    mul_one := fun a => Quotientₓ.induction_on' a fun a => congr_argₓ mk (mul_oneₓ a),
    inv :=
      fun a =>
        Quotientₓ.liftOn' a (fun a => ((a⁻¹ : G) : Quotientₓ N))
          fun a b hab =>
            Quotientₓ.sound'
              (by 
                show (a⁻¹⁻¹*b⁻¹) ∈ N 
                rw [←mul_inv_rev]
                exact N.inv_mem (nN.mem_comm hab)) }

@[toAdditive QuotientAddGroup.addGroup]
instance  : Groupₓ (Quotientₓ N) :=
  { quotient.div_inv_monoid _ with
    mul_left_inv := fun a => Quotientₓ.induction_on' a fun a => congr_argₓ mk (mul_left_invₓ a) }

/-- The group homomorphism from `G` to `G/N`. -/
@[toAdditive QuotientAddGroup.mk' "The additive group homomorphism from `G` to `G/N`."]
def mk' : G →* Quotientₓ N :=
  MonoidHom.mk' QuotientGroup.mk fun _ _ => rfl

@[simp, toAdditive]
theorem coe_mk' : (mk' N : G → Quotientₓ N) = coeₓ :=
  rfl

@[simp, toAdditive]
theorem mk'_apply (x : G) : mk' N x = x :=
  rfl

/-- Two `monoid_hom`s from a quotient group are equal if their compositions with
`quotient_group.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext,
  toAdditive
      " Two `add_monoid_hom`s from an additive quotient group are equal if their\ncompositions with `add_quotient_group.mk'` are equal.\n\nSee note [partially-applied ext lemmas]. "]
theorem monoid_hom_ext ⦃f g : Quotientₓ N →* H⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  MonoidHom.ext$ fun x => QuotientGroup.induction_on x$ (MonoidHom.congr_fun h : _)

@[simp, toAdditive QuotientAddGroup.eq_zero_iff]
theorem eq_one_iff {N : Subgroup G} [nN : N.normal] (x : G) : (x : Quotientₓ N) = 1 ↔ x ∈ N :=
  by 
    refine' quotient_group.eq.trans _ 
    rw [mul_oneₓ, Subgroup.inv_mem_iff]

@[simp, toAdditive QuotientAddGroup.ker_mk]
theorem ker_mk : MonoidHom.ker (QuotientGroup.mk' N : G →* QuotientGroup.Quotient N) = N :=
  Subgroup.ext eq_one_iff

@[toAdditive QuotientAddGroup.eq_iff_sub_mem]
theorem eq_iff_div_mem {N : Subgroup G} [nN : N.normal] {x y : G} : (x : Quotientₓ N) = y ↔ x / y ∈ N :=
  by 
    refine' eq_comm.trans (quotient_group.eq.trans _)
    rw [nN.mem_comm_iff, div_eq_mul_inv]

omit nN

@[toAdditive QuotientAddGroup.addCommGroup]
instance  {G : Type _} [CommGroupₓ G] (N : Subgroup G) : CommGroupₓ (Quotientₓ N) :=
  { @QuotientGroup.Quotient.group _ _ N N.normal_of_comm with
    mul_comm := fun a b => Quotientₓ.induction_on₂' a b fun a b => congr_argₓ mk (mul_commₓ a b) }

include nN

local notation " Q " => Quotientₓ N

@[simp, toAdditive QuotientAddGroup.coe_zero]
theorem coe_one : ((1 : G) :  Q ) = 1 :=
  rfl

@[simp, toAdditive QuotientAddGroup.coe_add]
theorem coe_mul (a b : G) : ((a*b : G) :  Q ) = a*b :=
  rfl

@[simp, toAdditive QuotientAddGroup.coe_neg]
theorem coe_inv (a : G) : ((a⁻¹ : G) :  Q ) = a⁻¹ :=
  rfl

@[simp]
theorem coe_pow (a : G) (n : ℕ) : ((a ^ n : G) :  Q ) = a ^ n :=
  (mk' N).map_pow a n

@[simp]
theorem coe_zpow (a : G) (n : ℤ) : ((a ^ n : G) :  Q ) = a ^ n :=
  (mk' N).map_zpow a n

/-- A group homomorphism `φ : G →* H` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* H`. -/
@[toAdditive QuotientAddGroup.lift
      "An `add_group` homomorphism `φ : G →+ H` with `N ⊆ ker(φ)`\ndescends (i.e. `lift`s) to a group homomorphism `G/N →* H`."]
def lift (φ : G →* H) (HN : ∀ x _ : x ∈ N, φ x = 1) :  Q  →* H :=
  MonoidHom.mk'
    (fun q :  Q  =>
      q.lift_on' φ$
        fun a b hab : (a⁻¹*b) ∈ N =>
          calc φ a = φ a*1 := (mul_oneₓ _).symm 
            _ = φ a*φ (a⁻¹*b) := HN (a⁻¹*b) hab ▸ rfl 
            _ = φ (a*a⁻¹*b) := (φ.map_mul a (a⁻¹*b)).symm 
            _ = φ b :=
            by 
              rw [mul_inv_cancel_left]
            )
    fun q r => Quotientₓ.induction_on₂' q r$ φ.map_mul

@[simp, toAdditive QuotientAddGroup.lift_mk]
theorem lift_mk {φ : G →* H} (HN : ∀ x _ : x ∈ N, φ x = 1) (g : G) : lift N φ HN (g :  Q ) = φ g :=
  rfl

@[simp, toAdditive QuotientAddGroup.lift_mk']
theorem lift_mk' {φ : G →* H} (HN : ∀ x _ : x ∈ N, φ x = 1) (g : G) : lift N φ HN (mk g :  Q ) = φ g :=
  rfl

@[simp, toAdditive QuotientAddGroup.lift_quot_mk]
theorem lift_quot_mk {φ : G →* H} (HN : ∀ x _ : x ∈ N, φ x = 1) (g : G) : lift N φ HN (Quot.mk _ g :  Q ) = φ g :=
  rfl

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
@[toAdditive QuotientAddGroup.map
      "An `add_group` homomorphism `f : G →+ H` induces a map\n`G/N →+ H/M` if `N ⊆ f⁻¹(M)`."]
def map (M : Subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) : Quotientₓ N →* Quotientₓ M :=
  by 
    refine' QuotientGroup.lift N ((mk' M).comp f) _ 
    intro x hx 
    refine' QuotientGroup.eq.2 _ 
    rw [mul_oneₓ, Subgroup.inv_mem_iff]
    exact h hx

@[simp, toAdditive QuotientAddGroup.map_coe]
theorem map_coe (M : Subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
  map N M f h («expr↑ » x) = «expr↑ » (f x) :=
  lift_mk' _ _ x

@[toAdditive QuotientAddGroup.map_mk']
theorem map_mk' (M : Subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
  map N M f h (mk' _ x) = «expr↑ » (f x) :=
  QuotientGroup.lift_mk' _ _ x

omit nN

variable(φ : G →* H)

open Function MonoidHom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[toAdditive QuotientAddGroup.kerLift "The induced map from the quotient by the kernel to the\ncodomain."]
def ker_lift : Quotientₓ (ker φ) →* H :=
  lift _ φ$ fun g => φ.mem_ker.mp

@[simp, toAdditive QuotientAddGroup.ker_lift_mk]
theorem ker_lift_mk (g : G) : (ker_lift φ) g = φ g :=
  lift_mk _ _ _

@[simp, toAdditive QuotientAddGroup.ker_lift_mk']
theorem ker_lift_mk' (g : G) : (ker_lift φ) (mk g) = φ g :=
  lift_mk' _ _ _

@[toAdditive QuotientAddGroup.injective_ker_lift]
theorem ker_lift_injective : injective (ker_lift φ) :=
  fun a b =>
    Quotientₓ.induction_on₂' a b$
      fun a b h : φ a = φ b =>
        Quotientₓ.sound'$
          show (a⁻¹*b) ∈ ker φ by 
            rw [mem_ker, φ.map_mul, ←h, φ.map_inv, inv_mul_selfₓ]

/-- The induced map from the quotient by the kernel to the range. -/
@[toAdditive QuotientAddGroup.rangeKerLift "The induced map from the quotient by the kernel to\nthe range."]
def range_ker_lift : Quotientₓ (ker φ) →* φ.range :=
  lift _ φ.range_restrict$
    fun g hg =>
      (mem_ker _).mp$
        by 
          rwa [range_restrict_ker]

@[toAdditive QuotientAddGroup.range_ker_lift_injective]
theorem range_ker_lift_injective : injective (range_ker_lift φ) :=
  fun a b =>
    Quotientₓ.induction_on₂' a b$
      fun a b h : φ.range_restrict a = φ.range_restrict b =>
        Quotientₓ.sound'$
          show (a⁻¹*b) ∈ ker φ by 
            rw [←range_restrict_ker, mem_ker, φ.range_restrict.map_mul, ←h, φ.range_restrict.map_inv, inv_mul_selfₓ]

@[toAdditive QuotientAddGroup.range_ker_lift_surjective]
theorem range_ker_lift_surjective : surjective (range_ker_lift φ) :=
  by 
    rintro ⟨_, g, rfl⟩
    use mk g 
    rfl

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[toAdditive QuotientAddGroup.quotientKerEquivRange
      "The first isomorphism theorem\n(a definition): the canonical isomorphism between `G/(ker φ)` to `range φ`."]
noncomputable def quotient_ker_equiv_range : Quotientₓ (ker φ) ≃* range φ :=
  MulEquiv.ofBijective (range_ker_lift φ) ⟨range_ker_lift_injective φ, range_ker_lift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[toAdditive QuotientAddGroup.quotientKerEquivOfRightInverse
      "The canonical isomorphism\n`G/(ker φ) ≃+ H` induced by a homomorphism `φ : G →+ H` with a right inverse `ψ : H → G`.",
  simps]
def quotient_ker_equiv_of_right_inverse (ψ : H → G) (hφ : Function.RightInverse ψ φ) : Quotientₓ (ker φ) ≃* H :=
  { ker_lift φ with toFun := ker_lift φ, invFun := mk ∘ ψ,
    left_inv :=
      fun x =>
        ker_lift_injective φ
          (by 
            rw [Function.comp_app, ker_lift_mk', hφ]),
    right_inv := hφ }

/-- The canonical isomorphism `G/⊥ ≃* G`. -/
@[toAdditive QuotientAddGroup.quotientBot "The canonical isomorphism `G/⊥ ≃+ G`.", simps]
def quotient_bot : Quotientₓ (⊥ : Subgroup G) ≃* G :=
  quotient_ker_equiv_of_right_inverse (MonoidHom.id G) id fun x => rfl

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `quotient_group.quotient_ker_equiv_of_right_inverse`.
-/
@[toAdditive QuotientAddGroup.quotientKerEquivOfSurjective
      "The canonical isomorphism\n`G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.\n\nFor a `computable` version, see `quotient_add_group.quotient_ker_equiv_of_right_inverse`."]
noncomputable def quotient_ker_equiv_of_surjective (hφ : Function.Surjective φ) : Quotientₓ (ker φ) ≃* H :=
  quotient_ker_equiv_of_right_inverse φ _ hφ.has_right_inverse.some_spec

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[toAdditive "If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are\nisomorphic."]
def equiv_quotient_of_eq {M N : Subgroup G} [M.normal] [N.normal] (h : M = N) : Quotientₓ M ≃* Quotientₓ N :=
  { toFun :=
      lift M (mk' N)
        fun m hm =>
          QuotientGroup.eq.mpr
            (by 
              simpa [←h] using M.inv_mem hm),
    invFun :=
      lift N (mk' M)
        fun n hn =>
          QuotientGroup.eq.mpr
            (by 
              simpa [←h] using N.inv_mem hn),
    left_inv :=
      fun x =>
        x.induction_on'$
          by 
            intro 
            rfl,
    right_inv :=
      fun x =>
        x.induction_on'$
          by 
            intro 
            rfl,
    map_mul' :=
      fun x y =>
        by 
          rw [map_mul] }

@[simp, toAdditive]
theorem equiv_quotient_of_eq_mk {M N : Subgroup G} [M.normal] [N.normal] (h : M = N) (x : G) :
  QuotientGroup.equivQuotientOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[toAdditive
      "Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,\nthen there is a map `A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions."]
def quotient_map_subgroup_of_of_le {A' A B' B : Subgroup G} [hAN : (A'.subgroup_of A).Normal]
  [hBN : (B'.subgroup_of B).Normal] (h' : A' ≤ B') (h : A ≤ B) :
  Quotientₓ (A'.subgroup_of A) →* Quotientₓ (B'.subgroup_of B) :=
  map _ _ (Subgroup.inclusion h)$
    by 
      simp [Subgroup.subgroupOf, Subgroup.comap_comap] <;> exact Subgroup.comap_mono h'

@[simp, toAdditive]
theorem quotient_map_subgroup_of_of_le_coe {A' A B' B : Subgroup G} [hAN : (A'.subgroup_of A).Normal]
  [hBN : (B'.subgroup_of B).Normal] (h' : A' ≤ B') (h : A ≤ B) (x : A) :
  quotient_map_subgroup_of_of_le h' h x = «expr↑ » (Subgroup.inclusion h x : B) :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.subgroup_of A : subgroup A)` depends on on `A`.
-/
@[toAdditive
      "Let `A', A, B', B` be subgroups of `G`.\nIf `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.\n\nApplying this equiv is nicer than rewriting along the equalities, since the type of\n`(A'.add_subgroup_of A : add_subgroup A)` depends on on `A`.\n"]
def equiv_quotient_subgroup_of_of_eq {A' A B' B : Subgroup G} [hAN : (A'.subgroup_of A).Normal]
  [hBN : (B'.subgroup_of B).Normal] (h' : A' = B') (h : A = B) :
  Quotientₓ (A'.subgroup_of A) ≃* Quotientₓ (B'.subgroup_of B) :=
  MonoidHom.toMulEquiv (quotient_map_subgroup_of_of_le h'.le h.le) (quotient_map_subgroup_of_of_le h'.ge h.ge)
    (by 
      ext ⟨x, hx⟩
      rfl)
    (by 
      ext ⟨x, hx⟩
      rfl)

section SndIsomorphismThm

open Subgroup

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`, where
`N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[toAdditive
      "The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`,\nwhere `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`"]
noncomputable def quotient_inf_equiv_prod_normal_quotient (H N : Subgroup G) [N.normal] :
  Quotientₓ ((H⊓N).comap H.subtype) ≃* Quotientₓ (N.comap (H⊔N).Subtype) :=
  let φ : H →* Quotientₓ (N.comap (H⊔N).Subtype) := (mk'$ N.comap (H⊔N).Subtype).comp (inclusion le_sup_left)
  have φ_surjective : Function.Surjective φ :=
    fun x =>
      x.induction_on'$
        by 
          rintro ⟨y, hy : y ∈ «expr↑ » (H⊔N)⟩
          rw [mul_normal H N] at hy 
          rcases hy with ⟨h, n, hh, hn, rfl⟩
          use h, hh 
          apply quotient.eq.mpr 
          change (h⁻¹*h*n) ∈ N 
          rwa [←mul_assocₓ, inv_mul_selfₓ, one_mulₓ]
  (equiv_quotient_of_eq
        (by 
          simp [comap_comap, ←comap_ker])).trans
    (quotient_ker_equiv_of_surjective φ φ_surjective)

end SndIsomorphismThm

section ThirdIsoThm

variable(M : Subgroup G)[nM : M.normal]

include nM nN

@[toAdditive QuotientAddGroup.map_normal]
instance map_normal : (M.map (QuotientGroup.mk' N)).Normal :=
  { conj_mem :=
      by 
        rintro _ ⟨x, hx, rfl⟩ y 
        refine' induction_on' y fun y => ⟨(y*x)*y⁻¹, Subgroup.Normal.conj_mem nM x hx y, _⟩
        simp only [mk'_apply, coe_mul, coe_inv] }

variable(h : N ≤ M)

/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[toAdditive QuotientAddGroup.quotientQuotientEquivQuotientAux
      "The map from the third isomorphism theorem for additive groups: `(A / N) / (M / N) → A / M`."]
def quotient_quotient_equiv_quotient_aux : Quotientₓ (M.map (mk' N)) →* Quotientₓ M :=
  lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by 
      rintro _ ⟨x, hx, rfl⟩
      rw [map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)

@[simp, toAdditive QuotientAddGroup.quotient_quotient_equiv_quotient_aux_coe]
theorem quotient_quotient_equiv_quotient_aux_coe (x : QuotientGroup.Quotient N) :
  quotient_quotient_equiv_quotient_aux N M h x = QuotientGroup.map N M (MonoidHom.id G) h x :=
  QuotientGroup.lift_mk' _ _ x

@[toAdditive QuotientAddGroup.quotient_quotient_equiv_quotient_aux_coe_coe]
theorem quotient_quotient_equiv_quotient_aux_coe_coe (x : G) :
  quotient_quotient_equiv_quotient_aux N M h (x : QuotientGroup.Quotient N) = x :=
  QuotientGroup.lift_mk' _ _ x

/-- **Noether's third isomorphism theorem** for groups: `(G / N) / (M / N) ≃ G / M`. -/
@[toAdditive QuotientAddGroup.quotientQuotientEquivQuotient
      "**Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃ A / M`."]
def quotient_quotient_equiv_quotient :
  QuotientGroup.Quotient (M.map (QuotientGroup.mk' N)) ≃* QuotientGroup.Quotient M :=
  MonoidHom.toMulEquiv (quotient_quotient_equiv_quotient_aux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by 
      ext 
      simp )
    (by 
      ext 
      simp )

end ThirdIsoThm

section trivialₓ

@[toAdditive]
theorem subsingleton_quotient_top : Subsingleton (QuotientGroup.Quotient (⊤ : Subgroup G)) :=
  Trunc.subsingleton

/-- If the quotient by a subgroup gives a singleton then the subgroup is the whole group. -/
@[toAdditive]
theorem subgroup_eq_top_of_subsingleton (H : Subgroup G) (h : Subsingleton (QuotientGroup.Quotient H)) : H = ⊤ :=
  top_unique$
    fun x _ =>
      have this : (1⁻¹*x) ∈ H := QuotientGroup.eq.1 (Subsingleton.elimₓ _ _)
      by 
        rwa [one_inv, one_mulₓ] at this

end trivialₓ

end QuotientGroup

