/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Localization.Integral
import Mathbin.RingTheory.Localization.AtPrime
import Mathbin.Order.Minimal

/-!

# Minimal primes

We provide various results concerning the minimal primes above an ideal

## Main results
- `ideal.minimal_primes`: `I.minimal_primes` is the set of ideals that are minimal primes over `I`.
- `minimal_primes`: `minimal_primes R` is the set of minimal primes of `R`.
- `ideal.exists_minimal_primes_le`: Every prime ideal over `I` contains a minimal prime over `I`.
- `ideal.radical_minimal_primes`: The minimal primes over `I.radical` are precisely
  the minimal primes over `I`.
- `ideal.Inf_minimal_primes`: The intersection of minimal primes over `I` is `I.radical`.
- `ideal.exists_minimal_primes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `ideal.minimal_primes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.


-/


section

variable {R S : Type _} [CommRing R] [CommRing S] (I J : Ideal R)

/-- `I.minimal_primes` is the set of ideals that are minimal primes over `I`. -/
def Ideal.MinimalPrimes : Set (Ideal R) :=
  Minimals (· ≤ ·) { p | p.IsPrime ∧ I ≤ p }

/-- `minimal_primes R` is the set of minimal primes of `R`.
This is defined as `ideal.minimal_primes ⊥`. -/
def MinimalPrimes (R : Type _) [CommRing R] : Set (Ideal R) :=
  Ideal.MinimalPrimes ⊥

variable {I J}

theorem Ideal.exists_minimal_primes_le [J.IsPrime] (e : I ≤ J) : ∃ p ∈ I.MinimalPrimes, p ≤ J := by
  suffices
    ∃ m ∈ { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ OrderDual.ofDual p },
      OrderDual.toDual J ≤ m ∧ ∀ z ∈ { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ p }, m ≤ z → z = m
    by
    obtain ⟨p, h₁, h₂, h₃⟩ := this
    simp_rw [← @eq_comm _ p] at h₃
    exact ⟨p, ⟨h₁, fun a b c => (h₃ a b c).le⟩, h₂⟩
  apply zorn_nonempty_partial_order₀
  swap
  · refine' ⟨show J.is_prime by infer_instance, e⟩
    
  rintro (c : Set (Ideal R)) hc hc' J' hJ'
  refine' ⟨OrderDual.toDual (Inf c), ⟨Ideal.Inf_is_prime_of_is_chain ⟨J', hJ'⟩ hc'.symm fun x hx => (hc hx).1, _⟩, _⟩
  · rw [OrderDual.of_dual_to_dual]
    convert le_Inf _
    intro x hx
    exact (hc hx).2
    
  · rintro z hz
    rw [OrderDual.le_to_dual]
    exact Inf_le hz
    

@[simp]
theorem Ideal.radical_minimal_primes : I.radical.MinimalPrimes = I.MinimalPrimes := by
  rw [Ideal.MinimalPrimes, Ideal.MinimalPrimes]
  congr
  ext p
  exact ⟨fun ⟨a, b⟩ => ⟨a, ideal.le_radical.trans b⟩, fun ⟨a, b⟩ => ⟨a, a.radical_le_iff.mpr b⟩⟩

@[simp]
theorem Ideal.Inf_minimal_primes : inf I.MinimalPrimes = I.radical := by
  rw [I.radical_eq_Inf]
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_Inf] at hx⊢
    rintro J ⟨e, hJ⟩
    skip
    obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimal_primes_le e
    exact hp' (hx hp)
    
  · apply Inf_le_Inf _
    intro I hI
    exact hI.1.symm
    

/- ./././Mathport/Syntax/Translate/Basic.lean:572:2: warning: expanding binder collection (p «expr ∈ » minimal_primes[minimal_primes] R) -/
theorem Ideal.exists_comap_eq_of_mem_minimal_primes_of_injective {f : R →+* S} (hf : Function.Injective f) (p)
    (_ : p ∈ MinimalPrimes R) : ∃ p' : Ideal S, p'.IsPrime ∧ p'.comap f = p := by
  haveI := H.1.1
  have : Nontrivial (Localization (Submonoid.map f p.prime_compl)) := by
    refine' ⟨⟨1, 0, _⟩⟩
    convert
      (IsLocalization.map_injective_of_injective p.prime_compl (Localization.AtPrime p)
            (Localization <| p.prime_compl.map f) hf).Ne
        one_ne_zero
    · rw [map_one]
      
    · rw [map_zero]
      
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization (Submonoid.map f p.prime_compl))
  skip
  refine' ⟨M.comap (algebraMap S <| Localization (Submonoid.map f p.prime_compl)), inferInstance, _⟩
  rw [Ideal.comap_comap, ←
    @IsLocalization.map_comp _ _ _ _ Localization.isLocalization _ p.prime_compl.le_comap_map _
      Localization.isLocalization,
    ← Ideal.comap_comap]
  suffices _ ≤ p by exact this.antisymm (H.2 ⟨inferInstance, bot_le⟩ this)
  intro x hx
  by_contra h
  apply hM.ne_top
  apply M.eq_top_of_is_unit_mem hx
  apply IsUnit.map
  apply IsLocalization.map_units _ (show p.prime_compl from ⟨x, h⟩)
  infer_instance

/- ./././Mathport/Syntax/Translate/Basic.lean:572:2: warning: expanding binder collection (p «expr ∈ » (I.comap f).minimal_primes) -/
theorem Ideal.exists_comap_eq_of_mem_minimal_primes {I : Ideal S} (f : R →+* S) (p)
    (_ : p ∈ (I.comap f).MinimalPrimes) : ∃ p' : Ideal S, p'.IsPrime ∧ I ≤ p' ∧ p'.comap f = p := by
  haveI := H.1.1
  let f' := I f
  have e : (I f).ker = I.comap f := by
    ext1
    exact Submodule.Quotient.mk_eq_zero _
  have : (I f).ker ≤ p := by
    rw [Ideal.mk_ker, e]
    exact H.1.2
  obtain ⟨p', hp₁, hp₂⟩ :=
    Ideal.exists_comap_eq_of_mem_minimal_primes_of_injective (I f).ker_lift_injective (p.map (I f).ker) _
  · skip
    refine' ⟨p'.comap I, Ideal.IsPrime.comap _, _, _⟩
    · exact ideal.mk_ker.symm.trans_le (Ideal.comap_mono bot_le)
      
    convert congr_arg (Ideal.comap (I f).ker) hp₂
    rwa [Ideal.comap_map_of_surjective (I f).ker Ideal.Quotient.mk_surjective, eq_comm, sup_eq_left]
    
  refine' ⟨⟨_, bot_le⟩, _⟩
  · apply Ideal.map_is_prime_of_surjective _ this
    exact Ideal.Quotient.mk_surjective
    
  · rintro q ⟨hq, -⟩ hq'
    rw [← Ideal.map_comap_of_surjective (I f).ker Ideal.Quotient.mk_surjective q]
    apply Ideal.map_mono
    skip
    apply H.2
    · refine' ⟨inferInstance, (ideal.mk_ker.trans e).symm.trans_le (Ideal.comap_mono bot_le)⟩
      
    · refine' (Ideal.comap_mono hq').trans _
      rw [Ideal.comap_map_of_surjective]
      exacts[sup_le rfl.le this, Ideal.Quotient.mk_surjective]
      
    

/- ./././Mathport/Syntax/Translate/Basic.lean:572:2: warning: expanding binder collection (p «expr ∈ » (I.comap f).minimal_primes) -/
theorem Ideal.exists_minimal_primes_comap_eq {I : Ideal S} (f : R →+* S) (p) (_ : p ∈ (I.comap f).MinimalPrimes) :
    ∃ p' ∈ I.MinimalPrimes, Ideal.comap f p' = p := by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimal_primes f p H
  skip
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimal_primes_le h₂
  refine' ⟨q, hq, Eq.symm _⟩
  haveI := hq.1.1
  have := (Ideal.comap_mono hq').trans_eq h₃
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.1.2⟩ this).antisymm this

theorem Ideal.mimimal_primes_comap_of_surjective {f : R →+* S} (hf : Function.Surjective f) {I J : Ideal S}
    (h : J ∈ I.MinimalPrimes) : J.comap f ∈ (I.comap f).MinimalPrimes := by
  haveI := h.1.1
  refine' ⟨⟨inferInstance, Ideal.comap_mono h.1.2⟩, _⟩
  rintro K ⟨hK, e₁⟩ e₂
  have : f.ker ≤ K := (Ideal.comap_mono bot_le).trans e₁
  rw [← sup_eq_left.mpr this, RingHom.ker_eq_comap_bot, ← Ideal.comap_map_of_surjective f hf]
  apply Ideal.comap_mono _
  apply h.2 _ _
  · exact ⟨Ideal.map_is_prime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
    
  · exact Ideal.map_le_of_le_comap e₂
    

theorem Ideal.comap_minimal_primes_eq_of_surjective {f : R →+* S} (hf : Function.Surjective f) (I : Ideal S) :
    (I.comap f).MinimalPrimes = Ideal.comap f '' I.MinimalPrimes := by
  ext J
  constructor
  · intro H
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimal_primes_comap_eq f J H
    exact ⟨p, h, rfl⟩
    
  · rintro ⟨J, hJ, rfl⟩
    exact Ideal.mimimal_primes_comap_of_surjective hf hJ
    

theorem Ideal.minimal_primes_eq_comap : I.MinimalPrimes = Ideal.comap I '' MinimalPrimes (R ⧸ I) := by
  rw [MinimalPrimes, ← Ideal.comap_minimal_primes_eq_of_surjective Ideal.Quotient.mk_surjective, ←
    RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem Ideal.minimal_primes_eq_subsingleton (hI : I.IsPrimary) : I.MinimalPrimes = {I.radical} := by
  ext J
  constructor
  · exact fun H =>
      let e := H.1.1.radical_le_iff.mpr H.1.2
      (H.2 ⟨Ideal.is_prime_radical hI, Ideal.le_radical⟩ e).antisymm e
    
  · rintro (rfl : J = I.radical)
    exact ⟨⟨Ideal.is_prime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩
    

theorem Ideal.minimal_primes_eq_subsingleton_self [I.IsPrime] : I.MinimalPrimes = {I} := by
  ext J
  constructor
  · exact fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.1.2).antisymm H.1.2
    
  · rintro (rfl : J = I)
    refine' ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩
    

end

