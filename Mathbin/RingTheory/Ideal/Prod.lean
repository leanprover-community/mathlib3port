import Mathbin.RingTheory.Ideal.Operations

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form.  Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/


universe u v

variable {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (I I' : Ideal R) (J J' : Ideal S)

namespace Ideal

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/-- `I × J` as an ideal of `R × S`. -/
  def
    Prod
    : Ideal R × S
    :=
      {
        Carrier := { x | x.fst ∈ I ∧ x.snd ∈ J } ,
          zero_mem' := by simp ,
          add_mem'
              :=
              by
                rintro ⟨ a₁ , a₂ ⟩ ⟨ b₁ , b₂ ⟩ ⟨ ha₁ , ha₂ ⟩ ⟨ hb₁ , hb₂ ⟩
                  exact ⟨ I.add_mem ha₁ hb₁ , J.add_mem ha₂ hb₂ ⟩
            ,
          smul_mem'
            :=
            by rintro ⟨ a₁ , a₂ ⟩ ⟨ b₁ , b₂ ⟩ ⟨ hb₁ , hb₂ ⟩ exact ⟨ I.mul_mem_left _ hb₁ , J.mul_mem_left _ hb₂ ⟩
        }

@[simp]
theorem mem_prod {r : R} {s : S} : (⟨r, s⟩ : R × S) ∈ Prod I J ↔ r ∈ I ∧ s ∈ J :=
  Iff.rfl

@[simp]
theorem prod_top_top : Prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤ :=
  Ideal.ext$
    by 
      simp 

/-- Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be explicitly
    given as the image under the projection maps. -/
theorem ideal_prod_eq (I : Ideal (R × S)) : I = Ideal.prod (map (RingHom.fst R S) I) (map (RingHom.snd R S) I) :=
  by 
    apply Ideal.ext 
    rintro ⟨r, s⟩
    rw [mem_prod, mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjectiveₓ,
      mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
    refine' ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, _⟩
    rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩⟩
    simpa using I.add_mem (I.mul_mem_left (1, 0) h₁) (I.mul_mem_left (0, 1) h₂)

@[simp]
theorem map_fst_prod (I : Ideal R) (J : Ideal S) : map (RingHom.fst R S) (Prod I J) = I :=
  by 
    ext 
    rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjectiveₓ]
    exact
      ⟨by 
          rintro ⟨x, ⟨h, rfl⟩⟩
          exact h.1,
        fun h => ⟨⟨x, 0⟩, ⟨⟨h, Ideal.zero_mem _⟩, rfl⟩⟩⟩

@[simp]
theorem map_snd_prod (I : Ideal R) (J : Ideal S) : map (RingHom.snd R S) (Prod I J) = J :=
  by 
    ext 
    rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
    exact
      ⟨by 
          rintro ⟨x, ⟨h, rfl⟩⟩
          exact h.2,
        fun h => ⟨⟨0, x⟩, ⟨⟨Ideal.zero_mem _, h⟩, rfl⟩⟩⟩

@[simp]
theorem map_prod_comm_prod : map (↑(RingEquiv.prodComm : R × S ≃+* S × R)) (Prod I J) = Prod J I :=
  by 
    refine' trans (ideal_prod_eq _) _ 
    simp [map_map]

/-- Ideals of `R × S` are in one-to-one correspondence with pairs of ideals of `R` and ideals of
    `S`. -/
def ideal_prod_equiv : Ideal (R × S) ≃ Ideal R × Ideal S :=
  { toFun := fun I => ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩, invFun := fun I => Prod I.1 I.2,
    left_inv := fun I => (ideal_prod_eq I).symm,
    right_inv :=
      fun ⟨I, J⟩ =>
        by 
          simp  }

@[simp]
theorem ideal_prod_equiv_symm_apply (I : Ideal R) (J : Ideal S) : ideal_prod_equiv.symm ⟨I, J⟩ = Prod I J :=
  rfl

theorem Prod.ext_iff {I I' : Ideal R} {J J' : Ideal S} : Prod I J = Prod I' J' ↔ I = I' ∧ J = J' :=
  by 
    simp only [←ideal_prod_equiv_symm_apply, ideal_prod_equiv.symm.injective.eq_iff, Prod.mk.inj_iffₓ]

theorem is_prime_of_is_prime_prod_top {I : Ideal R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime) : I.is_prime :=
  by 
    constructor
    ·
      (
        contrapose! h)
      simp [is_prime_iff, h]
    ·
      intro x y hxy 
      have  : ((⟨x, 1⟩ : R × S)*⟨y, 1⟩) ∈ Prod I ⊤
      ·
        rw [Prod.mk_mul_mk, mul_oneₓ, mem_prod]
        exact ⟨hxy, trivialₓ⟩
      simpa using h.mem_or_mem this

theorem is_prime_of_is_prime_prod_top' {I : Ideal S} (h : (Ideal.prod (⊤ : Ideal R) I).IsPrime) : I.is_prime :=
  by 
    apply @is_prime_of_is_prime_prod_top _ R 
    rw [←map_prod_comm_prod]
    exact map_is_prime_of_equiv _

theorem is_prime_ideal_prod_top {I : Ideal R} [h : I.is_prime] : (Prod I (⊤ : Ideal S)).IsPrime :=
  by 
    constructor
    ·
      (
        rcases h with ⟨h, -⟩
        contrapose! h)
      rw [←prod_top_top, Prod.ext_iff] at h 
      exact h.1
    rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨h₁, h₂⟩
    cases' h.mem_or_mem h₁ with h h
    ·
      exact Or.inl ⟨h, trivialₓ⟩
    ·
      exact Or.inr ⟨h, trivialₓ⟩

theorem is_prime_ideal_prod_top' {I : Ideal S} [h : I.is_prime] : (Prod (⊤ : Ideal R) I).IsPrime :=
  by 
    rw [←map_prod_comm_prod]
    apply map_is_prime_of_equiv _ 
    exact is_prime_ideal_prod_top

theorem ideal_prod_prime_aux {I : Ideal R} {J : Ideal S} : (Ideal.prod I J).IsPrime → I = ⊤ ∨ J = ⊤ :=
  by 
    contrapose! 
    simp only [ne_top_iff_one, is_prime_iff, not_and, not_forall, not_or_distrib]
    exact
      fun ⟨hI, hJ⟩ hIJ =>
        ⟨⟨0, 1⟩, ⟨1, 0⟩,
          by 
            simp ,
          by 
            simp [hJ],
          by 
            simp [hI]⟩

/-- Classification of prime ideals in product rings: the prime ideals of `R × S` are precisely the
    ideals of the form `p × S` or `R × p`, where `p` is a prime ideal of `R` or `S`. -/
theorem ideal_prod_prime (I : Ideal (R × S)) :
  I.is_prime ↔ (∃ p : Ideal R, p.is_prime ∧ I = Ideal.prod p ⊤) ∨ ∃ p : Ideal S, p.is_prime ∧ I = Ideal.prod ⊤ p :=
  by 
    constructor
    ·
      rw [ideal_prod_eq I]
      intros hI 
      rcases ideal_prod_prime_aux hI with (h | h)
      ·
        right 
        rw [h] at hI⊢
        exact ⟨_, ⟨is_prime_of_is_prime_prod_top' hI, rfl⟩⟩
      ·
        left 
        rw [h] at hI⊢
        exact ⟨_, ⟨is_prime_of_is_prime_prod_top hI, rfl⟩⟩
    ·
      rintro (⟨p, ⟨h, rfl⟩⟩ | ⟨p, ⟨h, rfl⟩⟩)
      ·
        exact is_prime_ideal_prod_top
      ·
        exact is_prime_ideal_prod_top'

@[simp]
private def prime_ideals_equiv_impl :
  Sum { I : Ideal R // I.is_prime } { J : Ideal S // J.is_prime } → { K : Ideal (R × S) // K.is_prime }
| Sum.inl ⟨I, hI⟩ =>
  ⟨Ideal.prod I ⊤,
    by 
      exact is_prime_ideal_prod_top⟩
| Sum.inr ⟨J, hJ⟩ =>
  ⟨Ideal.prod ⊤ J,
    by 
      exact is_prime_ideal_prod_top'⟩

section 

variable (R S)

/-- The prime ideals of `R × S` are in bijection with the disjoint union of the prime ideals
    of `R` and the prime ideals of `S`. -/
noncomputable def prime_ideals_equiv :
  { K : Ideal (R × S) // K.is_prime } ≃ Sum { I : Ideal R // I.is_prime } { J : Ideal S // J.is_prime } :=
  Equivₓ.symm$
    Equivₓ.ofBijective prime_ideals_equiv_impl
      (by 
        constructor
        ·
          rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;> simp [Prod.ext_iff] at h
          ·
            simp [h]
          ·
            exact False.elim (hI.ne_top h.1)
          ·
            exact False.elim (hJ.ne_top h.2)
          ·
            simp [h]
        ·
          rintro ⟨I, hI⟩
          rcases(ideal_prod_prime I).1 hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          ·
            exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
          ·
            exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)

end 

@[simp]
theorem prime_ideals_equiv_symm_inl (h : I.is_prime) :
  (prime_ideals_equiv R S).symm (Sum.inl ⟨I, h⟩) =
    ⟨Prod I ⊤,
      by 
        exact is_prime_ideal_prod_top⟩ :=
  rfl

@[simp]
theorem prime_ideals_equiv_symm_inr (h : J.is_prime) :
  (prime_ideals_equiv R S).symm (Sum.inr ⟨J, h⟩) =
    ⟨Prod ⊤ J,
      by 
        exact is_prime_ideal_prod_top'⟩ :=
  rfl

end Ideal

