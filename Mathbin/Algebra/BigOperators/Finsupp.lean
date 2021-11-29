import Mathbin.Data.Finsupp.Basic 
import Mathbin.Algebra.BigOperators.Pi 
import Mathbin.Algebra.BigOperators.Ring

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/


open_locale BigOperators

variable {α ι γ A B C : Type _} [AddCommMonoidₓ A] [AddCommMonoidₓ B] [AddCommMonoidₓ C]

variable {t : ι → A → C} (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x+y) = t i x+t i y)

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

theorem Finset.sum_apply' : (∑k in s, f k) i = ∑k in s, f k i :=
  (Finsupp.applyAddHom i : (ι →₀ A) →+ A).map_sum f s

theorem Finsupp.sum_apply' : g.sum k x = g.sum fun i b => k i b x :=
  Finset.sum_apply _ _ _

section 

include h0 h1

open_locale Classical

theorem Finsupp.sum_sum_index' : (∑x in s, f x).Sum t = ∑x in s, (f x).Sum t :=
  Finset.induction_on s rfl$
    fun a s has ih =>
      by 
        simpRw [Finset.sum_insert has, Finsupp.sum_add_index h0 h1, ih]

end 

section 

variable {R S : Type _} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} : (s.sum f*b) = s.sum fun a c => f a c*b :=
  by 
    simp only [Finsupp.sum, Finset.sum_mul]

theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} : (b*s.sum f) = s.sum fun a c => b*f a c :=
  by 
    simp only [Finsupp.sum, Finset.mul_sum]

end 

