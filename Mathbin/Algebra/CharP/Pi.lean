import Mathbin.Algebra.CharP.Basic
import Mathbin.Algebra.Ring.Pi

/-!
# Characteristic of semirings of functions
-/


universe u v

namespace CharP

instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiringₓ R] (p : ℕ) [CharP R p] : CharP (ι → R) p :=
  ⟨fun x =>
    let ⟨i⟩ := hi
    Iff.symm $
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext $ fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι → R) = 0 by
              rw [RingHom.map_nat_cast, h],
          fun h =>
          (Pi.evalRingHom (fun _ : ι => R) i).map_nat_cast x ▸ by
            rw [h, RingHom.map_zero]⟩⟩

instance pi' (ι : Type u) [hi : Nonempty ι] (R : Type v) [CommRingₓ R] (p : ℕ) [CharP R p] : CharP (ι → R) p :=
  CharP.pi ι R p

end CharP

