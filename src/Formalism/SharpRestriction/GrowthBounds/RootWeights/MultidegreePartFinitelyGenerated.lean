module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowerMonomialExpansion
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowerPadicValuationBound
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def halfFactorialValuation (p : ℕ) {σ : Type} (m : σ →₀ ℕ) : WithTop ℚ := (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)

theorem mem_fock_lattice_iff_coeff {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    InBB (O := O) p F ↔ ∀ m, 0 ≤ vK p (F.coeff m) + halfFactorialValuation p m := by
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  rw [InBB, vBB, Finset.le_inf_iff]
  constructor
  · intro h m
    by_cases hm : m ∈ F.support
    · exact h m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm, hV0, top_add]
      exact le_top
  · intro h m _
    exact h m

theorem fock_lattice_zero_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} : InBB (O := O) p (0 : MvPolynomial σ (KK O)) := by
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  refine (mem_fock_lattice_iff_coeff hV 0).2 fun m => ?_
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, hV0, top_add, le_top]

theorem fock_lattice_add_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} {F G : MvPolynomial σ (KK O)}
    (hF : InBB (O := O) p F) (hG : InBB (O := O) p G) : InBB (O := O) p (F + G) := by
  obtain ⟨-, -, hVadd, -, -, -⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV] at hF hG ⊢
  intro m
  rw [MvPolynomial.coeff_add]
  calc (0 : WithTop ℚ)
      ≤ min (vK p (F.coeff m) + halfFactorialValuation p m) (vK p (G.coeff m) + halfFactorialValuation p m) := le_min (hF m) (hG m)
    _ = min (vK p (F.coeff m)) (vK p (G.coeff m)) + halfFactorialValuation p m := min_add_add_right _ _ _
    _ ≤ vK p (F.coeff m + G.coeff m) + halfFactorialValuation p m := add_le_add_left (hVadd _ _) _

theorem fock_lattice_sum_mem {p : ℕ} (hV : ValuationProperties p O) {σ α : Type} (s : Finset α) (f : α → MvPolynomial σ (KK O))
    (h : ∀ i ∈ s, InBB (O := O) p (f i)) : InBB (O := O) p (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (InBB (O := O) p) (fun _ _ => fock_lattice_add_mem hV) (fock_lattice_zero_mem hV) h

theorem fock_lattice_smul_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (o : O) {F : MvPolynomial σ (KK O)}
    (hF : InBB (O := O) p F) : InBB (O := O) p (o • F) := by
  obtain ⟨-, hVmul, -, -, -, hVint⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV] at hF ⊢
  intro m
  rw [coeff_smul, Algebra.smul_def, hVmul]
  have ho : 0 ≤ vK p (algebraMap O (KK O) o) := (hVint _).2 ⟨o, rfl⟩
  calc (0 : WithTop ℚ) ≤ vK p (F.coeff m) + halfFactorialValuation p m := hF m
    _ ≤ vK p (algebraMap O (KK O) o) + vK p (F.coeff m) + halfFactorialValuation p m :=
        add_le_add_left (le_add_of_nonneg_left ho) _

theorem fock_lattice_monomial_iff {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (m : σ →₀ ℕ) (c : KK O) :
    InBB (O := O) p (monomial m c) ↔ 0 ≤ vK p c + halfFactorialValuation p m := by
  classical
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV]
  constructor
  · intro h
    have hm := h m
    rwa [coeff_monomial, if_pos rfl] at hm
  · intro h m'
    rw [coeff_monomial]
    split_ifs with hm
    · rw [← hm]
      exact h
    · rw [hV0, top_add]
      exact le_top

theorem fock_lattice_iff_monomials {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    InBB (O := O) p F ↔ ∀ m, InBB (O := O) p (monomial m (F.coeff m)) := by
  rw [mem_fock_lattice_iff_coeff hV]
  exact forall_congr' fun m => (fock_lattice_monomial_iff hV m _).symm

theorem fock_lattice_linear_map_closed {p : ℕ} (hV : ValuationProperties p O) {σ : Type}
    (u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O))
    (h : ∀ m c, InBB (O := O) p (monomial m c) → InBB (O := O) p (u (monomial m c)))
    (F : MvPolynomial σ (KK O)) (hF : InBB (O := O) p F) : InBB (O := O) p (u F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← F.support_sum_monomial_coeff, map_sum]
  exact fock_lattice_sum_mem hV _ _ fun m _ => h m _ ((fock_lattice_iff_monomials hV F).1 hF m)

theorem valuation_intCast_padicVal {p : ℕ} (hV : ValuationProperties p O) (z : ℤ) (hz : z ≠ 0) :
    vK p (z : KK O) = ((padicValInt p z : ℚ) : WithTop ℚ) := by
  obtain ⟨-, -, -, hVnat, hVneg, -⟩ := id hV
  have hn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz
  have e : padicValInt p z = padicValNat p z.natAbs := by
    simp [padicValInt, padicValNat]
  rw [e]
  rcases Int.natAbs_eq z with h | h
  · conv_lhs => rw [h]
    rw [Int.cast_natCast]
    exact hVnat _ hn
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast, hVneg]
    exact hVnat _ hn

theorem fock_lattice_monomial_rescale {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (m m' : σ →₀ ℕ) (c : KK O) (z : ℤ)
    (h : InBB (O := O) p (monomial m c))
    (hz : z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) :
    InBB (O := O) p (monomial m' (c * (z : KK O))) := by
  obtain ⟨hV0, hVmul, -, -, -, -⟩ := id hV
  rw [fock_lattice_monomial_iff hV] at h ⊢
  by_cases hz0 : z = 0
  · rw [hz0, Int.cast_zero, mul_zero, hV0, top_add]
    exact le_top
  have hz' : padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m') :=
    hz.resolve_left hz0
  rw [hVmul, valuation_intCast_padicVal hV z hz0]
  have hq : ((padicValNat p (expFact m) : ℚ) / 2) ≤
      (padicValInt p z : ℚ) + (padicValNat p (expFact m') : ℚ) / 2 := by
    have : (padicValNat p (expFact m) : ℚ) ≤ 2 * (padicValInt p z : ℚ) + padicValNat p (expFact m') := by
      exact_mod_cast hz'
    linarith
  have hw : halfFactorialValuation p m ≤ ((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m' := by
    simp only [halfFactorialValuation]
    rw [← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 hq
  calc (0 : WithTop ℚ) ≤ vK p c + halfFactorialValuation p m := h
    _ ≤ vK p c + (((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m') := add_le_add_right hw _
    _ = vK p c + ((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m' := (add_assoc _ _ _).symm

theorem mem_integral_poly_iff_map {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ IntPol O σ ↔ ∃ F0 : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) F0 = F := by
  simp only [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply]
  rfl

theorem mem_integral_poly_iff_coeff {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ IntPol O σ ↔ ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o := by
  rw [mem_integral_poly_iff_map]
  constructor
  · rintro ⟨F0, rfl⟩ m
    exact ⟨F0.coeff m, coeff_map _ _ _⟩
  · intro h
    choose g hg using h
    refine ⟨∑ m ∈ F.support, monomial m (g m), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [← F.support_sum_monomial_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_monomial, hg]

theorem integer_monomial_mem_integral {σ : Type} (m : σ →₀ ℕ) (z : ℤ) : monomial m (z : KK O) ∈ IntPol O σ := by
  exact (mem_integral_poly_iff_map _).2 ⟨monomial m (z : O), by rw [map_monomial, map_intCast]⟩

theorem integral_poly_linear_map_closed {σ : Type} (u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O))
    (h : ∀ m, u (monomial m 1) ∈ IntPol O σ) (F : MvPolynomial σ (KK O)) (hF : F ∈ IntPol O σ) :
    u F ∈ IntPol O σ := by
  choose g hg using (mem_integral_poly_iff_coeff F).1 hF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← F.support_sum_monomial_coeff, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  have e : monomial m (F.coeff m) = (algebraMap O (KK O) (g m)) • monomial m (1 : KK O) := by
    rw [smul_monomial, smul_eq_mul, mul_one, hg]
  rw [e, map_smul, algebraMap_smul]
  exact Submodule.smul_mem _ _ (h m)

theorem fock_lattice_closure_holds {p : ℕ} (hV : ValuationProperties p O) : FockLatticeClosure p O :=
  fun _ => ⟨fock_lattice_zero_mem hV, fun _ _ => fock_lattice_add_mem hV, fun o _ => fock_lattice_smul_mem hV o,
  fun m c => fock_lattice_monomial_iff hV m c, fock_lattice_iff_monomials hV, fun u h F hF => fock_lattice_linear_map_closed hV u h F hF,
  fun m m' c z h hz => fock_lattice_monomial_rescale hV m m' c z h hz, fun u h F hF => integral_poly_linear_map_closed u h F hF,
  fun m z => integer_monomial_mem_integral m z, mem_integral_poly_iff_coeff⟩

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem choose_factorial_identity (α β f : ℕ) (h : f ≤ β) :
    β.choose f * ((β - f).factorial * (α + f).factorial) = (α + f).choose f * (β.factorial * α.factorial) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left f α)
  rw [Nat.add_sub_cancel] at h2
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos f)
  calc f.factorial * (β.choose f * ((β - f).factorial * (α + f).factorial))
      = (β.choose f * f.factorial * (β - f).factorial) * (α + f).factorial := by ring
    _ = β.factorial * (α + f).factorial := by rw [h1]
    _ = β.factorial * ((α + f).choose f * f.factorial * α.factorial) := by rw [h2]
    _ = f.factorial * ((α + f).choose f * (β.factorial * α.factorial)) := by ring

theorem product_two_coordinates_swap {n : ℕ} (g g' : Fin n → ℕ) (a b : Fin n) (hab : a ≠ b)
    (h : ∀ c, c ≠ a → c ≠ b → g' c = g c) :
    (∏ c, g' c) * (g a * g b) = (∏ c, g c) * (g' a * g' b) := by
  classical
  have hs : ∀ f : Fin n → ℕ, ∏ c, f c = f a * f b * ∏ c ∈ (univ.erase a).erase b, f c := by
    intro f
    rw [← Finset.mul_prod_erase univ f (mem_univ a),
      ← Finset.mul_prod_erase (univ.erase a) f (mem_erase.2 ⟨hab.symm, mem_univ b⟩)]
    ring
  have hrest : ∏ c ∈ (univ.erase a).erase b, g' c = ∏ c ∈ (univ.erase a).erase b, g c :=
    prod_congr rfl fun c hc => h c (ne_of_mem_erase (mem_of_mem_erase hc)) (ne_of_mem_erase hc)
  rw [hs g', hs g, hrest]
  ring

theorem sum_single_apply_section {ι : Type} {n : ℕ} (g : ι → ι × Fin n) (hg : ∀ l, (g l).1 = l) (f : ι →₀ ℕ)
    (v : ι × Fin n) [Decidable (v = g v.1)] :
    (∑ l ∈ f.support, Finsupp.single (g l) (f l)) v = if v = g v.1 then f v.1 else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  have key : ∀ l, g l = v → l = v.1 ∧ v = g v.1 := by
    rintro l rfl
    exact ⟨(hg l).symm, by rw [hg l]⟩
  split_ifs with hv
  · rw [Finset.sum_eq_single v.1]
    · rw [← hv, Finsupp.single_eq_same]
    · intro l _ hl
      rw [Finsupp.single_apply, if_neg]
      exact fun h => hl (key l h).1
    · intro hnot
      simp only [Finsupp.mem_support_iff, not_not] at hnot
      simp [hnot]
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hv (key l h).2

theorem exponent_factorial_eq_prod {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    expFact m = ∏ l : ι, ∏ c : Fin n, (m (l, c)).factorial := by
  classical
  unfold expFact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]

theorem exponent_factorial_ne_zero {σ : Type} (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _

theorem divided_power_padic_valuation_bound {ι : Type} [Fintype ι] {n : ℕ} (p : ℕ) [Fact p.Prime] (src dst : ι → ι × Fin n)
    (hs : ∀ l, (src l).1 = l) (hd : ∀ l, (dst l).1 = l) (hne : ∀ l, src l ≠ dst l)
    (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (zf : ι → ℤ) (hz : ∀ l, (zf l).natAbs = (m (src l)).choose (f l)) :
    (∏ l ∈ f.support, zf l) = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p (∏ l ∈ f.support, zf l) +
      padicValNat p (expFact ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
        ∑ l ∈ f.support, Finsupp.single (dst l) (f l))) := by
  classical
  by_cases hall : ∀ l ∈ f.support, f l ≤ m (src l)
  swap
  ·
    left
    push_neg at hall
    obtain ⟨l, hl, hlt⟩ := hall
    apply Finset.prod_eq_zero hl
    have := hz l
    rw [Nat.choose_eq_zero_of_lt hlt] at this
    exact Int.natAbs_eq_zero.1 this
  have hall' : ∀ l, f l ≤ m (src l) := fun l => by
    by_cases hl : l ∈ f.support
    · exact hall l hl
    · simp only [Finsupp.mem_support_iff, not_not] at hl
      rw [hl]
      exact Nat.zero_le _
  right
  have hm' : ∀ x : ι × Fin n, ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l)) x =
      (m x - (if x = src x.1 then f x.1 else 0)) + (if x = dst x.1 then f x.1 else 0) := by
    intro x
    rw [Finsupp.add_apply, Finsupp.tsub_apply, sum_single_apply_section src hs f x, sum_single_apply_section dst hd f x]
  set m' : ι × Fin n →₀ ℕ := (m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l) with hm'def

  have hrow : ∀ l, (∏ c, (m (l, c)).factorial) * (m (dst l) + f l).choose (f l) =
      (∏ c, (m' (l, c)).factorial) * (m (src l)).choose (f l) := by
    intro l
    obtain ⟨a, ha⟩ : ∃ a, src l = (l, a) := ⟨(src l).2, Prod.ext (hs l) rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, dst l = (l, b) := ⟨(dst l).2, Prod.ext (hd l) rfl⟩
    have hab : a ≠ b := fun h => hne l (by rw [ha, hb, h])
    have hma : m' (l, a) = m (l, a) - f l := by
      rw [hm']; simp [ha, hb, hab]
    have hmb : m' (l, b) = m (l, b) + f l := by
      rw [hm']; simp [ha, hb, hab, Ne.symm hab]
    have hmc : ∀ c, c ≠ a → c ≠ b → m' (l, c) = m (l, c) := by
      intro c hca hcb
      rw [hm']; simp [ha, hb, hca, hcb]
    have hF : f l ≤ m (l, a) := ha ▸ hall' l
    have h2 := product_two_coordinates_swap (fun c => (m (l, c)).factorial) (fun c => (m' (l, c)).factorial) a b hab
      (fun c hca hcb => by simp only [hmc c hca hcb])
    beta_reduce at h2
    rw [hma, hmb] at h2
    have h3 := choose_factorial_identity (m (l, b)) (m (l, a)) (f l) hF
    rw [ha, hb]
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos (Nat.factorial_pos (m (l, a))) (Nat.factorial_pos (m (l, b))))
    calc (∏ c, (m (l, c)).factorial) * (m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)
        = (∏ c, (m (l, c)).factorial) * ((m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by ring
      _ = (∏ c, (m (l, c)).factorial) * ((m (l, a)).choose (f l) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by rw [h3]
      _ = (m (l, a)).choose (f l) * ((∏ c, (m (l, c)).factorial) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by ring
      _ = (m (l, a)).choose (f l) * ((∏ c, (m' (l, c)).factorial) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by rw [h2]
      _ = (∏ c, (m' (l, c)).factorial) * (m (l, a)).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial) := by ring
  have htot : expFact m * ∏ l, (m (dst l) + f l).choose (f l) =
      expFact m' * ∏ l, (m (src l)).choose (f l) := by
    rw [exponent_factorial_eq_prod m, exponent_factorial_eq_prod m', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ => hrow l
  have hY : (∏ l ∈ f.support, zf l).natAbs = ∏ l, (m (src l)).choose (f l) := by
    have hnat : (∏ l ∈ f.support, zf l).natAbs = ∏ l ∈ f.support, (zf l).natAbs := by
      first
        | exact map_prod Int.natAbsHom zf f.support
        | simpa using map_prod Int.natAbsHom zf f.support
    rw [hnat, Finset.prod_congr rfl (fun l _ => hz l)]
    refine Finset.prod_subset (Finset.subset_univ _) fun l _ hl => ?_
    simp only [Finsupp.mem_support_iff, not_not] at hl
    rw [hl, Nat.choose_zero_right]
  have hX0 : ∏ l, (m (dst l) + f l).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (Nat.le_add_left _ _)).ne'
  have hY0 : ∏ l, (m (src l)).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (hall' l)).ne'
  have hv := congrArg (padicValNat p) htot
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (exponent_factorial_ne_zero m) hX0, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (exponent_factorial_ne_zero m') hY0] at hv
  rw [show padicValInt p (∏ l ∈ f.support, zf l) =
    padicValNat p (∏ l ∈ f.support, zf l).natAbs from by
      rw [padicValInt, Nat.padicValNat_def], hY]
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem monomial_eq_smul_basis {K σ : Type} [CommRing K] (m : σ →₀ ℕ) (c : K) :
    monomial m c = c • (basisMonomials σ K m) := by
  rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem divided_power_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    divPow K LL S a b k (monomial m c) = c • divPowMono K LL S a b k m := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold divPow
  rw [Module.Basis.constr_basis]

theorem binomial_operator_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    binomPol K LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : K)) := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold binomPol
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

def dividedPowerTermCoefficient {ι : Type} {n : ℕ} (LL : Letters ι) (a b : Fin n) (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (l : ι) : ℤ :=
  if LL.vec l then ((m (l, b)).choose (f l) : ℤ) else (-1 : ℤ) ^ (f l) * ((m (l, a)).choose (f l) : ℤ)

open Classical in
theorem divided_power_monomial_expansion {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    c • divPowMono K LL S a b k m =
      ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
        monomial ((m - ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, b) else (l, a)) (f l))
          + ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, a) else (l, b)) (f l))
          (c * ((∏ l ∈ f.support, dividedPowerTermCoefficient LL a b m f l : ℤ) : K)) := by
  unfold divPowMono
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.smul_monomial, smul_eq_mul, Int.cast_prod]
  congr 2
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold dividedPowerTermCoefficient
  split_ifs <;> push_cast <;> rfl

theorem integral_formula_stability_holds {p : ℕ} (hp : p.Prime) (hV : ValuationProperties p O) : PolynomialIntegralFormPreservesLattices p O := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro n ι _ LL S
  refine ⟨?_, ?_⟩
  · intro u hu x hx
    refine integral_poly_linear_map_closed u (fun m => ?_) x hx
    rcases hu with ⟨a, b, k, -, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [one_mul]
      exact integer_monomial_mem_integral _ _
    · rw [binomial_operator_monomial, one_mul]
      exact integer_monomial_mem_integral _ _
  · intro u hu F hF
    refine fock_lattice_linear_map_closed hV u (fun m c hmc => ?_) F hF
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine fock_lattice_sum_mem hV _ _ fun f _ => ?_
      refine fock_lattice_monomial_rescale hV m _ c _ hmc ?_
      exact divided_power_padic_valuation_bound p (fun l => if LL.vec l then (l, b) else (l, a))
        (fun l => if LL.vec l then (l, a) else (l, b))
        (fun l => by split_ifs <;> rfl) (fun l => by split_ifs <;> rfl)
        (fun l => by split_ifs <;> simp [hab, Ne.symm hab]) m f (dividedPowerTermCoefficient LL a b m f)
        (fun l => by unfold dividedPowerTermCoefficient; split_ifs <;> simp [Int.natAbs_mul, Int.natAbs_pow])
    · rw [binomial_operator_monomial]
      exact fock_lattice_monomial_rescale hV m m c _ hmc (Or.inr (Nat.le_add_left _ _))

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def fockLattice {p : ℕ} (hV : ValuationProperties p O) (σ : Type) : Submodule O (MvPolynomial σ (KK O)) where
  carrier := {F | InBB (O := O) p F}
  zero_mem' := fock_lattice_zero_mem hV
  add_mem' := fun hF hG => fock_lattice_add_mem hV hF hG
  smul_mem' := fun o _ hF => fock_lattice_smul_mem hV o hF

theorem multidegree_monomials_finite {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) :
    {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i}.Finite := by
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin n => d x.1))).subset ?_
  intro m hm
  rw [Set.mem_Iic, Finsupp.le_def]
  rintro ⟨i, c⟩
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [← hm i]
  exact Finset.single_le_sum (f := fun c' => m (i, c')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem multidegree_part_finitely_generated {p : ℕ} (hp0 : (p : KK O) ≠ 0) {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) (N : ℕ)
    (h : ∀ F ∈ L, ∀ m, (∀ i, multideg m i = d i) → ∃ o : O, (p : KK O) ^ N * F.coeff m = algebraMap O (KK O) o) :
    (latticeMultidegreePart L d).FG := by
  classical
  set S := (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset with hS
  let f : ↥(Pol (KK O) n d) →ₗ[O] (S → KK O) :=
    { toFun := fun F s => (p : KK O) ^ N * (F : MvPolynomial (ι × Fin n) (KK O)).coeff s.1
      map_add' := fun F G => by
        funext s
        simp [mul_add]
      map_smul' := fun o F => by
        funext s
        simp [MvPolynomial.coeff_smul, mul_smul_comm] }
  let g : (S → O) →ₗ[O] (S → KK O) :=
    LinearMap.pi (fun s => (Algebra.linearMap O (KK O)).comp (LinearMap.proj s))
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    apply Subtype.ext
    ext m
    simp only [Submodule.coe_zero, MvPolynomial.coeff_zero]
    by_cases hm : m ∈ S
    · have h0 := congrFun hF ⟨m, hm⟩
      change (p : KK O) ^ N * (F : MvPolynomial _ (KK O)).coeff m = 0 at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp0)
    · by_contra hne
      apply hm
      have hF2 : (F : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := F.2
      have hsupp : m ∈ (F : MvPolynomial _ (KK O)).support := MvPolynomial.mem_support_iff.2 hne
      exact (Set.Finite.mem_toFinset _).2 (((MvPolynomial.mem_restrictSupport_iff _).1 hF2) (Finset.mem_coe.2 hsupp))
  have hle : (latticeMultidegreePart L d).map f ≤ LinearMap.range g := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : MvPolynomial (ι × Fin n) (KK O)) ∈ L := hx
    choose o ho using fun s : S => h _ hx' s.1 ((Set.Finite.mem_toFinset _).1 s.2)
    refine ⟨o, ?_⟩
    funext s
    exact (ho s).symm
  have hW : (LinearMap.range g).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map g
  haveI : IsNoetherian O (LinearMap.range g) := isNoetherian_of_fg_of_noetherian _ hW
  have h1 : (((latticeMultidegreePart L d).map f).comap (LinearMap.range g).subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map (LinearMap.range g).subtype
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
  exact Submodule.fg_of_fg_map_injective f hinj h2

theorem multidegree_part_spans {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ)
    (h : ∀ m, monomial m (1 : KK O) ∈ L) : MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  have hx : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
      MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := x.2
  have key : ∀ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support,
      monomial m (1 : KK O) ∈ Pol (KK O) n d := by
    intro m hm
    show monomial m (1 : KK O) ∈ MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i}
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_coe] at hm'
    have hm'' := MvPolynomial.support_monomial_subset hm'
    rw [Finset.mem_singleton] at hm''
    subst hm''
    exact ((MvPolynomial.mem_restrictSupport_iff _).1 hx) (Finset.mem_coe.2 hm)
  have hx2 : x = ∑ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support.attach,
      (x : MvPolynomial (ι × Fin n) (KK O)).coeff m.1 •
        (⟨monomial m.1 1, key m.1 m.2⟩ : Pol (KK O) n d) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [Finset.sum_attach _ (fun m => monomial m ((x : MvPolynomial (ι × Fin n) (KK O)).coeff m))]
    exact (x : MvPolynomial (ι × Fin n) (KK O)).as_sum
  rw [hx2]
  show _ ∈ Submodule.span (KK O) _
  refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact h m.1

theorem fock_lattice_finite_spanning_holds {p : ℕ} (hp : p.Prime) (S0 : UniformizedDVR p O) (hV : ValuationProperties p O) : FockLatticeFiniteSpanning p O := by
  intro n ι _
  have hp0 : (p : KK O) ≠ 0 := by
    intro h0
    have h1 := hV.2.2.2.1 p hp.ne_zero
    rw [h0, hV.1] at h1
    exact WithTop.top_ne_coe h1
  have hv1 : vK p (1 : KK O) = 0 := by
    have h1 := hV.2.2.2.1 1 one_ne_zero
    rw [Nat.cast_one, Nat.padicValNat_def, multiplicity_one_right] at h1
    simpa using h1
  have key : ∀ (x : WithTop ℚ) (a b : ℚ), 0 ≤ x + (a : WithTop ℚ) → a ≤ b → 0 ≤ (b : WithTop ℚ) + x := by
    intro x a b hx hab
    induction x using WithTop.recTopCoe with
    | top => simp
    | coe q =>
      rw [← WithTop.coe_add] at hx ⊢
      rw [WithTop.coe_nonneg] at hx ⊢
      linarith
  have hmono : ∀ m : ι × Fin n →₀ ℕ, monomial m (1 : KK O) ∈ fockLattice hV (ι × Fin n) := by
    intro m
    show InBB (O := O) p (monomial m (1 : KK O))
    rw [fock_lattice_monomial_iff hV, hv1, zero_add]
    unfold halfFactorialValuation
    exact WithTop.coe_nonneg.2 (by positivity)
  refine ⟨fockLattice hV (ι × Fin n), fun F => Iff.rfl, fun d => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact multidegree_part_finitely_generated hp0 _ d 0 (fun F hF m _ => by simpa using (mem_integral_poly_iff_coeff F).1 hF m)
  · exact multidegree_part_spans _ d (fun m => by simpa using integer_monomial_mem_integral (O := O) m 1)
  · refine multidegree_part_finitely_generated hp0 _ d
      (∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m)) ?_
    intro F hF m hm
    have hF' : InBB (O := O) p F := hF
    have h0 := (mem_fock_lattice_iff_coeff hV F).1 hF' m
    unfold halfFactorialValuation at h0
    apply (hV.2.2.2.2.2 _).1
    haveI := Fact.mk hp
    rw [hV.2.1, ← Nat.cast_pow, hV.2.2.2.1 _ (pow_ne_zero _ hp.ne_zero), Nat.padicValNat_def, Nat.multiplicity_prime_pow]
    refine key _ _ _ h0 ?_
    have hmS : m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset := (Set.Finite.mem_toFinset _).2 hm
    have hle := Finset.single_le_sum (f := fun m => padicValNat p (expFact m)) (fun _ _ => Nat.zero_le _) hmS
    have hle' : (padicValNat p (expFact m) : ℚ) ≤
        ((∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m) : ℕ) : ℚ) := by
      exact_mod_cast hle
    have hnn : (0 : ℚ) ≤ padicValNat p (expFact m) := by positivity
    linarith
  · exact multidegree_part_spans _ d hmono

end Formalism.MainNotions.G.GLWeightTheory
