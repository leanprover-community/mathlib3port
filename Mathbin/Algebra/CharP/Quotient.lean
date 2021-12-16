import Mathbin.Algebra.CharP.Basic 
import Mathbin.RingTheory.Ideal.Quotient

/-!
# Characteristic of quotients rings
-/


universe u v

namespace CharP

theorem Quotientₓ (R : Type u) [CommRingₓ R] (p : ℕ) [hp1 : Fact p.prime] (hp2 : ↑p ∈ Nonunits R) :
  CharP (R ⧸ (Ideal.span {p} : Ideal R)) p :=
  have hp0 : (p : R ⧸ (Ideal.span {p} : Ideal R)) = 0 :=
    (Ideal.Quotient.mk (Ideal.span {p} : Ideal R)).map_nat_cast p ▸
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span$ Set.mem_singleton _)
  ringChar.of_eq$
    Or.resolve_left ((Nat.dvd_prime hp1.1).1$ ringChar.dvd hp0)$
      fun h1 =>
        hp2$
          is_unit_iff_dvd_one.2$
            Ideal.mem_span_singleton.1$
              Ideal.Quotient.eq_zero_iff_mem.1$ @Subsingleton.elimₓ (@CharP.subsingleton _$ ringChar.of_eq h1) _ _

/-- If an ideal does not contain any coercions of natural numbers other than zero, then its quotient
inherits the characteristic of the underlying ring. -/
theorem quotient' {R : Type _} [CommRingₓ R] (p : ℕ) [CharP R p] (I : Ideal R)
  (h : ∀ x : ℕ, (x : R) ∈ I → (x : R) = 0) : CharP (R ⧸ I) p :=
  ⟨fun x =>
      by 
        rw [←cast_eq_zero_iff R p x, ←(Ideal.Quotient.mk I).map_nat_cast]
        refine' quotient.eq'.trans (_ : ↑x - 0 ∈ I ↔ _)
        rw [sub_zero]
        exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩⟩

end CharP

