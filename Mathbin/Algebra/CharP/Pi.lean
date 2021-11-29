import Mathbin.Algebra.CharP.Basic 
import Mathbin.Algebra.Ring.Pi

/-!
# Characteristic of semirings of functions
-/


universe u v

namespace CharP

-- error in Algebra.CharP.Pi: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance pi (ι : Type u) [hi : nonempty ι] (R : Type v) [semiring R] (p : exprℕ()) [char_p R p] : char_p (ι → R) p :=
⟨λ x, let ⟨i⟩ := hi in
 «expr $ »(iff.symm, (char_p.cast_eq_zero_iff R p x).symm.trans ⟨λ
   h, «expr $ »(funext, λ
    j, show «expr = »(pi.eval_ring_hom (λ
      _, R) j («expr↑ »(x) : ι → R), 0), by rw ["[", expr ring_hom.map_nat_cast, ",", expr h, "]"] []), λ
   h, «expr ▸ »((pi.eval_ring_hom (λ
      _ : ι, R) i).map_nat_cast x, by rw ["[", expr h, ",", expr ring_hom.map_zero, "]"] [])⟩)⟩

instance pi' (ι : Type u) [hi : Nonempty ι] (R : Type v) [CommRingₓ R] (p : ℕ) [CharP R p] : CharP (ι → R) p :=
  CharP.pi ι R p

end CharP

