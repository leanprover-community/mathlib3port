import Mathbin.GroupTheory.QuotientGroup 
import Mathbin.SetTheory.Fincard

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.

## Main definitions

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relindex K` : the relative index of `H : subgroup G` in `K : subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relindex_mul_relindex` : `relindex` is multiplicative in towers

-/


namespace Subgroup

open_locale Cardinal

variable {G : Type _} [Groupₓ G] (H K L : Subgroup G)

/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[toAdditive "The index of a subgroup as a natural number,\nand returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
  Nat.card (QuotientGroup.Quotient H)

/-- The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite. -/
@[toAdditive
      "The relative index of a subgroup as a natural number,\n  and returns 0 if the relative index is infinite."]
noncomputable def relindex : ℕ :=
  (H.subgroup_of K).index

-- error in GroupTheory.Index: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem index_comap_of_surjective
{G' : Type*}
[group G']
{f : «expr →* »(G', G)}
(hf : function.surjective f) : «expr = »((H.comap f).index, H.index) :=
begin
  letI [] [] [":=", expr quotient_group.left_rel H],
  letI [] [] [":=", expr quotient_group.left_rel (H.comap f)],
  have [ident key] [":", expr ∀
   x
   y : G', «expr ↔ »(setoid.r x y, setoid.r (f x) (f y))] [":=", expr λ
   x y, iff_of_eq (congr_arg ((«expr ∈ » H)) (by rw ["[", expr f.map_mul, ",", expr f.map_inv, "]"] []))],
  refine [expr cardinal.to_nat_congr (equiv.of_bijective (quotient.map' f (λ x y, (key x y).mp)) ⟨_, _⟩)],
  { simp_rw ["[", "<-", expr quotient.eq', "]"] ["at", ident key],
    refine [expr quotient.ind' (λ x, _)],
    refine [expr quotient.ind' (λ y, _)],
    exact [expr (key x y).mpr] },
  { refine [expr quotient.ind' (λ x, _)],
    obtain ["⟨", ident y, ",", ident hy, "⟩", ":=", expr hf x],
    exact [expr ⟨y, (quotient.map'_mk' f _ y).trans (congr_arg quotient.mk' hy)⟩] }
end

@[toAdditive]
theorem index_comap {G' : Type _} [Groupₓ G'] (f : G' →* G) : (H.comap f).index = H.relindex f.range :=
  Eq.trans
    (congr_argₓ index
      (by 
        rfl))
    ((H.subgroup_of f.range).index_comap_of_surjective f.range_restrict_surjective)

variable {H K L}

@[toAdditive]
theorem relindex_mul_index (h : H ≤ K) : (H.relindex K*K.index) = H.index :=
  ((mul_commₓ _ _).trans (Cardinal.to_nat_mul _ _).symm).trans
    (congr_argₓ Cardinal.toNat (Equiv.cardinal_eq (quotient_equiv_prod_of_le h))).symm

@[toAdditive]
theorem index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relindex K) (relindex_mul_index h)

@[toAdditive]
theorem relindex_subgroup_of (hKL : K ≤ L) : (H.subgroup_of L).relindex (K.subgroup_of L) = H.relindex K :=
  ((index_comap (H.subgroup_of L) (inclusion hKL)).trans (congr_argₓ _ (inclusion_range hKL))).symm

@[toAdditive]
theorem relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) : (H.relindex K*K.relindex L) = H.relindex L :=
  by 
    rw [←relindex_subgroup_of hKL]
    exact relindex_mul_index fun x hx => hHK hx

variable (H K L)

theorem inf_relindex_right : (H⊓K).relindex K = H.relindex K :=
  by 
    rw [←subgroup_of_map_subtype, relindex, relindex, subgroup_of, comap_map_eq_self_of_injective]
    exact Subtype.coe_injective

theorem inf_relindex_left : (H⊓K).relindex H = K.relindex H :=
  by 
    rw [inf_comm, inf_relindex_right]

theorem inf_relindex_eq_relindex_sup [K.normal] : (H⊓K).relindex H = K.relindex (H⊔K) :=
  Cardinal.to_nat_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv

theorem relindex_eq_relindex_sup [K.normal] : K.relindex H = K.relindex (H⊔K) :=
  by 
    rw [←inf_relindex_left, inf_relindex_eq_relindex_sup]

variable {H K}

theorem relindex_dvd_of_le_left (hHK : H ≤ K) : K.relindex L ∣ H.relindex L :=
  by 
    apply dvd_of_mul_left_eq ((H⊓L).relindex (K⊓L))
    rw [←inf_relindex_right H L, ←inf_relindex_right K L]
    exact relindex_mul_relindex (inf_le_inf_right L hHK) inf_le_right

variable (H K)

@[simp, toAdditive]
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Cardinal.to_nat_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[simp, toAdditive]
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Cardinal.to_nat_congr QuotientGroup.quotientBot.toEquiv

@[toAdditive]
theorem index_bot_eq_card [Fintype G] : (⊥ : Subgroup G).index = Fintype.card G :=
  index_bot.trans Nat.card_eq_fintype_card

@[simp, toAdditive]
theorem relindex_top_left : (⊤ : Subgroup G).relindex H = 1 :=
  index_top

@[simp, toAdditive]
theorem relindex_top_right : H.relindex ⊤ = H.index :=
  by 
    rw [←relindex_mul_index (show H ≤ ⊤ from le_top), index_top, mul_oneₓ]

@[simp, toAdditive]
theorem relindex_bot_left : (⊥ : Subgroup G).relindex H = Nat.card H :=
  by 
    rw [relindex, bot_subgroup_of, index_bot]

@[toAdditive]
theorem relindex_bot_left_eq_card [Fintype H] : (⊥ : Subgroup G).relindex H = Fintype.card H :=
  H.relindex_bot_left.trans Nat.card_eq_fintype_card

@[simp, toAdditive]
theorem relindex_bot_right : H.relindex ⊥ = 1 :=
  by 
    rw [relindex, subgroup_of_bot_eq_top, index_top]

@[simp, toAdditive]
theorem relindex_self : H.relindex H = 1 :=
  by 
    rw [relindex, subgroup_of_self, index_top]

@[simp, toAdditive card_mul_index]
theorem card_mul_index : (Nat.card H*H.index) = Nat.card G :=
  by 
    rw [←relindex_bot_left, ←index_bot]
    exact relindex_mul_index bot_le

@[toAdditive]
theorem index_map {G' : Type _} [Groupₓ G'] (f : G →* G') : (H.map f).index = (H⊔f.ker).index*f.range.index :=
  by 
    rw [←comap_map_eq, index_comap, relindex_mul_index (H.map_le_range f)]

@[toAdditive]
theorem index_map_dvd {G' : Type _} [Groupₓ G'] {f : G →* G'} (hf : Function.Surjective f) :
  (H.map f).index ∣ H.index :=
  by 
    rw [index_map, f.range_top_of_surjective hf, index_top, mul_oneₓ]
    exact index_dvd_of_le le_sup_left

@[toAdditive]
theorem dvd_index_map {G' : Type _} [Groupₓ G'] {f : G →* G'} (hf : f.ker ≤ H) : H.index ∣ (H.map f).index :=
  by 
    rw [index_map, sup_of_le_left hf]
    apply dvd_mul_right

@[toAdditive]
theorem index_map_eq {G' : Type _} [Groupₓ G'] {f : G →* G'} (hf1 : Function.Surjective f) (hf2 : f.ker ≤ H) :
  (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[toAdditive]
theorem index_eq_card [Fintype (QuotientGroup.Quotient H)] : H.index = Fintype.card (QuotientGroup.Quotient H) :=
  Nat.card_eq_fintype_card

@[toAdditive]
theorem index_mul_card [Fintype G] [hH : Fintype H] : (H.index*Fintype.card H) = Fintype.card G :=
  by 
    rw [←relindex_bot_left_eq_card, ←index_bot_eq_card, mul_commₓ] <;> exact relindex_mul_index bot_le

@[toAdditive]
theorem index_dvd_card [Fintype G] : H.index ∣ Fintype.card G :=
  by 
    classical 
    exact ⟨Fintype.card H, H.index_mul_card.symm⟩

variable {H}

@[simp]
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h => QuotientGroup.subgroup_eq_top_of_subsingleton H (Cardinal.to_nat_eq_one_iff_unique.mp h).1,
    fun h => (congr_argₓ index h).trans index_top⟩

theorem index_ne_zero_of_fintype [hH : Fintype (QuotientGroup.Quotient H)] : H.index ≠ 0 :=
  by 
    rw [index_eq_card]
    exact Fintype.card_ne_zero

theorem one_lt_index_of_ne_top [Fintype (QuotientGroup.Quotient H)] (hH : H ≠ ⊤) : 1 < H.index :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_fintype, mt index_eq_one.mp hH⟩

end Subgroup

