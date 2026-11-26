module

public import Mathlib

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfPowDvd
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring

open Polynomial

variable {K : Type} [Field K]

theorem eq_X_mul_unit (s : PowerSeries K) (h0 : PowerSeries.constantCoeff s = 0)
    (h1 : PowerSeries.coeff 1 s ≠ 0) : ∃ u : PowerSeries K, IsUnit u ∧ s = PowerSeries.X * u := by
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr h0
  refine ⟨u, ?_, hu⟩
  have hc : PowerSeries.coeff 1 s = PowerSeries.constantCoeff u := by
    rw [hu]
    simp [PowerSeries.coeff_succ_X_mul]
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [hc] at h1
  exact isUnit_iff_ne_zero.mpr h1

private theorem algebraMap_powerSeries_self_eq_C {R : Type} [CommRing R] (a : R) :
    algebraMap R (PowerSeries R) a = PowerSeries.C a := by
  rfl

private theorem constantCoeff_aeval_eq_eval_constantCoeff (y : PowerSeries K) (r : K[X]) :
    PowerSeries.constantCoeff (Polynomial.aeval y r) = r.eval (PowerSeries.constantCoeff y) := by
  refine Polynomial.induction_on' r (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), map_add (f := _), hp, hq, Polynomial.eval_add]
  · rw [Polynomial.aeval_monomial, map_mul, map_pow, algebraMap_powerSeries_self_eq_C, PowerSeries.constantCoeff_C,
      Polynomial.eval_monomial]

theorem pow_dvd_of_order (r : K[X]) (c : K) (s : PowerSeries K)
    (h0 : PowerSeries.constantCoeff s = 0) (h1 : PowerSeries.coeff 1 s ≠ 0) (b : ℕ)
    (hb : (PowerSeries.X : PowerSeries K) ^ b ∣ Polynomial.aeval (PowerSeries.C c + s) r) :
    (Polynomial.X - Polynomial.C c) ^ b ∣ r := by
  obtain ⟨u, hu, hsu⟩ := eq_X_mul_unit s h0 h1
  have hsub : Polynomial.aeval (PowerSeries.C c + s) (Polynomial.X - Polynomial.C c) = s := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_self_eq_C, add_sub_cancel_left]
  induction b generalizing r with
  | zero => simp
  | succ b ih =>
    have hX : (PowerSeries.X : PowerSeries K) ∣ Polynomial.aeval (PowerSeries.C c + s) r :=
      (dvd_pow_self _ (Nat.succ_ne_zero b)).trans hb
    have hroot : r.IsRoot c := by
      rw [PowerSeries.X_dvd_iff, constantCoeff_aeval_eq_eval_constantCoeff, map_add (f := _), PowerSeries.constantCoeff_C, h0,
        add_zero] at hX
      exact hX
    obtain ⟨q, rfl⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    rw [map_mul, hsub] at hb
    have hb' : (PowerSeries.X : PowerSeries K) * PowerSeries.X ^ b ∣
        PowerSeries.X * (u * Polynomial.aeval (PowerSeries.C c + s) q) := by
      rw [← mul_assoc, ← hsu, ← pow_succ']
      exact hb
    have hq : (PowerSeries.X : PowerSeries K) ^ b ∣ Polynomial.aeval (PowerSeries.C c + s) q :=
      hu.dvd_mul_left.mp ((mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hb')
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih q hq)

theorem eq_zero_of_pow_dvd (r : K[X]) (cs : Finset K) (b : ℕ)
    (h : ∀ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b ∣ r) (hdeg : r.natDegree < cs.card * b) : r = 0 := by
  by_contra hr
  have hprod : (∏ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b) ∣ r := by
    refine Finset.prod_dvd_of_coprime ?_ h
    intro x _ y _ hxy
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit).pow
  have hdeg' : (∏ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b).natDegree = cs.card * b := by
    rw [Polynomial.natDegree_prod _ _ (fun c _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c))]
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_comm]
  have := Polynomial.natDegree_le_of_dvd hprod hr
  omega

theorem algHom_coe {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (φ : PowerSeries O →ₐ[O] A) (r : O[X]) :
    φ (r : PowerSeries O) = Polynomial.aeval (φ PowerSeries.X) r := by
  refine Polynomial.induction_on r (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
  · rw [Polynomial.coe_C, Polynomial.aeval_C, ← algebraMap_powerSeries_self_eq_C, φ.commutes]
  · rw [Polynomial.coe_add, map_add (f := _), map_add (f := _), hp, hq]
  · rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, map_mul, map_pow,
      ← algebraMap_powerSeries_self_eq_C, φ.commutes, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

private theorem aeval_map_algebraMap_eq_aeval {O : Type} [CommRing O] [Algebra O K] (y : PowerSeries K)
    (r : O[X]) : Polynomial.aeval y (r.map (algebraMap O K)) = Polynomial.aeval y r := by
  exact Polynomial.aeval_map_algebraMap K y r

theorem dvd_of_vanish {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) f (N : ℕ)
    (hres : PowerSeries.map (IsLocalRing.residue O) f = PowerSeries.X ^ N)
    (Z : Finset K) (hZ : Z.card = N) (φ : K → (PowerSeries O →ₐ[O] PowerSeries K))
    (s : K → PowerSeries K) (hφX : ∀ c ∈ Z, φ c PowerSeries.X = PowerSeries.C c + s c)
    (hs0 : ∀ c ∈ Z, PowerSeries.constantCoeff (s c) = 0)
    (hs1 : ∀ c ∈ Z, PowerSeries.coeff 1 (s c) ≠ 0)
    (hf : ∀ c ∈ Z, PowerSeries.X ∣ φ c f) (b : ℕ) (g : PowerSeries O)
    (hg : ∀ c ∈ Z, PowerSeries.X ^ b ∣ φ c g) :
    ∃ h : PowerSeries O, g = f ^ b * h := by
  have hmap : PowerSeries.map (IsLocalRing.residue O) (f ^ b) = PowerSeries.X ^ (N * b) := by
    rw [map_pow, hres, ← pow_mul]
  have hne : PowerSeries.map (IsLocalRing.residue O) (f ^ b) ≠ 0 := by
    rw [hmap]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hqr⟩ := PowerSeries.exists_isWeierstrassDivision g hne
  have hord : (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (f ^ b)).order.toNat
      = N * b := by
    have hm : PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (f ^ b)
        = PowerSeries.X ^ (N * b) := hmap
    rw [hm, PowerSeries.order_X_pow]
    rfl
  have hdeg : r.degree < (N * b : ℕ) := by
    have := hqr.degree_lt
    rwa [hord] at this
  have hg_eq : g = f ^ b * q + (r : PowerSeries O) := hqr.eq_mul_add
  have hr : r = 0 := by
    by_contra hr0
    have hnat : r.natDegree < N * b := (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hdeg
    have hdvd : ∀ c ∈ Z, (Polynomial.X - Polynomial.C c) ^ b ∣ r.map (algebraMap O K) := by
      intro c hc
      apply pow_dvd_of_order _ c (s c) (hs0 c hc) (hs1 c hc) b
      have h1 : φ c g = (φ c f) ^ b * φ c q + Polynomial.aeval (PowerSeries.C c + s c) r := by
        rw [hg_eq, map_add (f := _), map_mul, map_pow, algHom_coe, hφX c hc]
      have h2 : (PowerSeries.X : PowerSeries K) ^ b ∣ (φ c f) ^ b * φ c q :=
        dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hf c hc) b) _
      have h4 := hg c hc
      rw [h1] at h4
      rw [aeval_map_algebraMap_eq_aeval]
      exact (dvd_add_right h2).mp h4
    have hK : r.map (algebraMap O K) = 0 := by
      refine eq_zero_of_pow_dvd _ Z b hdvd ?_
      rw [hZ]
      exact lt_of_le_of_lt Polynomial.natDegree_map_le hnat
    exact hr0 (Polynomial.map_injective _ hinj (by rw [hK, Polynomial.map_zero]))
  exact ⟨q, by rw [hg_eq, hr, Polynomial.coe_zero, add_zero]⟩

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.NormLtOneIffToZMod
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.Cyc

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_lt_one_iff_toZMod (x : ℤ_[l]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by

  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_le_inv_of_lt_one (x : ℤ_[l]) (h : ‖x‖ < 1) : ‖x‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by

  rw [show (-((1 : ℕ) : ℤ)) = -1 by simp, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
  simpa using h

theorem teich (c : ℤ_[l]) (hc : ‖c‖ = 1) : ∃ ω : ℤ_[l], ω ^ (l - 1) = 1 ∧ ‖ω - c‖ < 1 := by

  classical
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hFdef
  have hc0 : PadicInt.toZMod c ≠ 0 := fun h0 => by
    have := (norm_lt_one_iff_toZMod c).mpr h0
    rw [hc] at this
    exact lt_irrefl _ this
  have hn : ‖((l - 1 : ℕ) : ℤ_[l])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    rw [norm_lt_one_iff_toZMod, map_natCast, ZMod.natCast_eq_zero_iff] at h
    have h2 := hl.out.two_le
    have := Nat.le_of_dvd (by omega) h
    omega
  have e1 : Polynomial.aeval c F = c ^ (l - 1) - 1 := by simp [hFdef]
  have e2 : Polynomial.aeval c (Polynomial.derivative F) = ((l - 1 : ℕ) : ℤ_[l]) * c ^ (l - 1 - 1) := by
    simp [hFdef, Polynomial.derivative_X_pow]
  have hF' : ‖Polynomial.aeval c (Polynomial.derivative F)‖ = 1 := by
    rw [e2, norm_mul, norm_pow, hc, one_pow, mul_one, hn]
  have hF : ‖Polynomial.aeval c F‖ < 1 := by
    rw [e1, norm_lt_one_iff_toZMod, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one hc0, sub_self]
  obtain ⟨z, hz, hzc, -⟩ := hensels_lemma (F := F) (a := c) (by rw [hF', one_pow]; exact hF)
  refine ⟨z, ?_, ?_⟩
  · simpa [hFdef, sub_eq_zero] using hz
  · rw [hF'] at hzc; exact hzc

theorem pow_approx (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : ‖u - 1‖ = (l : ℝ)⁻¹) (c : ℤ_[l]) (hc : ‖c - 1‖ < 1)
    (n : ℕ) : ∃ k : ℕ, ‖u ^ k - c‖ ≤ (l : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  have hp := hl.out
  have h3 : 3 ≤ l := by have := hp.two_le; omega

  have hu1 : u - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, hu]; simp
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hu1
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hrn : ‖r‖ = 1 := by
    have : ‖u - 1‖ = ‖r‖ * (l : ℝ)⁻¹ := by rw [← hr, pow_one, norm_mul, PadicInt.norm_p]
    rw [hu] at this
    have hne : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hlpos.ne'
    field_simp at this
    linarith

  set a : ℤ := ((PadicInt.toZModPow (n + 1) r).val : ℤ) with ha_def
  have ha_cast : (a : ZMod (l ^ (n + 1))) = PadicInt.toZModPow (n + 1) r := by
    rw [ha_def, Int.cast_natCast, ZMod.natCast_zmod_val]
  have ha : ¬ (l : ℤ) ∣ a := by
    intro hdvd
    have h1 : (a : ZMod (l ^ 1)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using hdvd
    have h2 : (a : ZMod (l ^ 1)) = PadicInt.toZModPow 1 r := by
      rw [← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply, ← ha_cast, map_intCast]
    rw [h2, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow, hrn] at h1
    have : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
      rw [Nat.cast_one, zpow_neg_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    linarith
  have hord : orderOf (1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a) = l ^ n :=
    ZMod.orderOf_one_add_mul_prime_pow hp 1 (by omega) a ha n
  have hub : PadicInt.toZModPow (n + 1) u = 1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a := by
    have : u = 1 + (l : ℤ_[l]) ^ 1 * r := by rw [pow_one, mul_comm]; rw [pow_one] at hr; rw [hr]; ring
    rw [this, map_add (f := _), map_one, map_mul, map_pow, map_natCast, ha_cast]

  have huu : IsUnit (PadicInt.toZModPow (n + 1) u) := by
    apply IsUnit.map
    rw [PadicInt.isUnit_iff]
    have : u = 1 + (u - 1) := by ring
    rw [this]
    have h1 : ‖(u - 1)‖ < ‖(1 : ℤ_[l])‖ := by
      rw [hu, norm_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    rw [← norm_one (α := ℤ_[l])]
    exact PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)
  have hcu : IsUnit (PadicInt.toZModPow (n + 1) c) := by
    apply IsUnit.map
    rw [PadicInt.isUnit_iff]
    have : c = 1 + (c - 1) := by ring
    rw [this]
    have h1 : ‖(c - 1)‖ < ‖(1 : ℤ_[l])‖ := by rw [norm_one]; exact hc
    rw [← norm_one (α := ℤ_[l])]
    exact PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)
  set U := huu.unit
  set C := hcu.unit
  have hdiv : l ^ 1 ∣ l ^ (n + 1) := pow_dvd_pow l (by omega)
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hker : ∀ x : ℤ_[l], ‖x - 1‖ < 1 → ∀ hx : IsUnit (PadicInt.toZModPow (n + 1) x), hx.unit ∈ (ZMod.unitsMap hdiv).ker := by
    intro x hx hxu
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, IsUnit.unit_spec]
    change ZMod.castHom hdiv (ZMod (l ^ 1)) (PadicInt.toZModPow (n + 1) x) = 1
    rw [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega),
      ← sub_eq_zero, ← map_one (PadicInt.toZModPow 1), ← map_sub, ← RingHom.mem_ker,
      PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    exact norm_le_inv_of_lt_one _ hx
  have hUk : U ∈ (ZMod.unitsMap hdiv).ker := hker u (by rw [hu]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) huu
  have hCk : C ∈ (ZMod.unitsMap hdiv).ker := hker c hc hcu

  have hcardG : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  have hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp]
  have hrange : (ZMod.unitsMap hdiv).range = ⊤ := MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective hdiv)
  have hcardK : Nat.card (ZMod.unitsMap hdiv).ker = l ^ n := by
    have h1 := Subgroup.card_mul_index (ZMod.unitsMap hdiv).ker
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hcardH, hcardG] at h1
    have hl1 : 0 < l - 1 := by omega
    exact Nat.eq_of_mul_eq_mul_right hl1 h1
  have hzp : Subgroup.zpowers U = (ZMod.unitsMap hdiv).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hUk
    · rw [hcardK, Nat.card_zpowers, ← orderOf_units, IsUnit.unit_spec, hub, hord]
  rw [← hzp, ← mem_powers_iff_mem_zpowers] at hCk
  obtain ⟨k, hk⟩ := hCk
  refine ⟨k, ?_⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_pow,
    sub_eq_zero]
  have := congrArg Units.val hk
  simpa [U, C] using this

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.Cyc
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.GenOfKiller
namespace Formalism.MainNotions.UnusedSlot80.UGen

theorem span_le_card {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {g : ℕ} (v : Fin g → M) (N : Submodule R M)
    (hN : N ≤ Submodule.span R (Set.range v)) :
    ∃ (g₀ : ℕ) (w : Fin g₀ → M), g₀ ≤ g ∧ (∀ i, w i ∈ N) ∧
      N = Submodule.span R (Set.range w) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    (N.comap (Finsupp.linearCombination R v))
  refine ⟨n, fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R), ?_, ?_, ?_⟩
  · have h1 := Module.finrank_eq_card_basis b
    have h2 := Submodule.finrank_le (N.comap (Finsupp.linearCombination R v))
    have h3 := Module.finrank_eq_card_basis
      (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    simp only [Fintype.card_fin] at h1 h3
    omega
  · intro i
    exact (b i).2
  · have hb : Submodule.span R (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
        N.comap (Finsupp.linearCombination R v) := by
      have e : (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
          (N.comap (Finsupp.linearCombination R v)).subtype '' Set.range b := by
        ext x; simp
      rw [e, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    have e2 : (Set.range fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R)) =
        (Finsupp.linearCombination R v) '' Set.range fun i => ((b i : _) : Fin g →₀ R) := by
      ext x; simp
    rw [e2, ← Submodule.map_span, hb, Submodule.map_comap_eq,
      Finsupp.range_linearCombination, inf_eq_right.mpr hN]

private theorem mkQ_mem_span_of_mem_sup_lemma {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (P : Submodule R V) (u : ι → V) {x : V} (hx : x ∈ Submodule.span R (Set.range u) ⊔ P) :
    P.mkQ x ∈ Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
  obtain ⟨a, ha, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
  have hp0 : P.mkQ p = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hp
  rw [map_add (f := _), hp0, add_zero]
  have hle : (Submodule.span R (Set.range u)).map P.mkQ ≤
      Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hle (Submodule.mem_map_of_mem ha)

theorem gen_of_killer {R V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] (Msub Psub Isub : Submodule R V) (hIM : Isub ≤ Msub)
    {ι : Type*} [Finite ι] (F : ι → V) (hfg : Msub ≤ Submodule.span R (Set.range F) ⊔ Psub)
    (lR t : R) {g : ℕ} (v : Fin g → V)
    (hK : ∀ f ∈ Isub, ∃ K : ℕ, (lR ^ K * t) • f ∈ Submodule.span R (Set.range v) ⊔ Psub)
    (hsat : ∀ K : ℕ, ∀ f ∈ Msub, (lR ^ K * t) • f ∈ Psub → f ∈ Psub) :
    ∃ (g₀ : ℕ) (J : Fin g₀ → V), g₀ ≤ g ∧ (∀ i, J i ∈ Isub) ∧
      ∀ f ∈ Isub, ∃ o : Fin g₀ → R, f - ∑ i, o i • J i ∈ Psub := by
  classical
  let W : Submodule R (V ⧸ Psub) := Submodule.span R (Set.range fun i => Psub.mkQ (v i))
  let B : ℕ → Submodule R (V ⧸ Psub) := fun K =>
    W.comap ((lR ^ K * t) • (LinearMap.id : (V ⧸ Psub) →ₗ[R] V ⧸ Psub))
  have hBmono : Monotone B := by
    intro K K' hKK' q hq
    change (lR ^ K * t) • q ∈ W at hq
    change (lR ^ K' * t) • q ∈ W
    have e : lR ^ K' * t = lR ^ (K' - K) * (lR ^ K * t) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hKK']
    rw [e, mul_smul]
    exact W.smul_mem _ hq
  have hmemB : ∀ f ∈ Isub, ∃ K, Psub.mkQ f ∈ B K := by
    intro f hf
    obtain ⟨K, hKf⟩ := hK f hf
    refine ⟨K, ?_⟩
    change (lR ^ K * t) • Psub.mkQ f ∈ W
    rw [← map_smul]
    exact mkQ_mem_span_of_mem_sup_lemma Psub v hKf
  have hIle : Isub.map Psub.mkQ ≤ Submodule.span R (Set.range fun i => Psub.mkQ (F i)) := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hq
    exact mkQ_mem_span_of_mem_sup_lemma Psub F (hfg (hIM hf))
  haveI hT : IsNoetherian R (Submodule.span R (Set.range fun i => Psub.mkQ (F i))) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  haveI hIN : IsNoetherian R (Isub.map Psub.mkQ) := isNoetherian_of_le hIle
  have hfgI : (Isub.map Psub.mkQ).FG :=
    (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
  obtain ⟨S, hS⟩ := hfgI
  have hSB : ∀ x ∈ S, ∃ K, x ∈ B K := by
    intro x hx
    have hxI : x ∈ Isub.map Psub.mkQ := by
      rw [← hS]; exact Submodule.subset_span (Finset.mem_coe.mpr hx)
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hxI
    exact hmemB f hf
  choose! Kf hKf using hSB
  obtain ⟨K, hIB⟩ : ∃ K, Isub.map Psub.mkQ ≤ B K := by
    refine ⟨S.sup Kf, ?_⟩
    rw [← hS, Submodule.span_le]
    intro x hx
    exact hBmono (Finset.le_sup (Finset.mem_coe.mp hx)) (hKf x (Finset.mem_coe.mp hx))
  have hN : Isub.map ((lR ^ K * t) • Psub.mkQ) ≤
      Submodule.span R (Set.range fun i => Psub.mkQ (v i)) := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    have h1 := hIB (Submodule.mem_map_of_mem hf)
    change (lR ^ K * t) • Psub.mkQ f ∈ W at h1
    rw [LinearMap.smul_apply]
    exact h1
  obtain ⟨g₀, w, hg₀, hwN, hNw⟩ := span_le_card (fun i => Psub.mkQ (v i)) _ hN
  have hJ : ∀ i, ∃ f ∈ Isub, ((lR ^ K * t) • Psub.mkQ) f = w i :=
    fun i => Submodule.mem_map.mp (hwN i)
  choose J hJI hJw using hJ
  refine ⟨g₀, J, hg₀, hJI, ?_⟩
  intro f hf
  have hφf : ((lR ^ K * t) • Psub.mkQ) f ∈ Submodule.span R (Set.range w) := by
    rw [← hNw]; exact Submodule.mem_map_of_mem hf
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (R := R)).mp hφf
  refine ⟨o, hsat K _ ?_ ?_⟩
  · apply hIM
    exact Isub.sub_mem hf (Isub.sum_mem fun i _ => Isub.smul_mem _ (hJI i))
  · have h0 : ((lR ^ K * t) • Psub.mkQ) (f - ∑ i, o i • J i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [map_smul, hJw]
      rw [ho, sub_self]
    rw [LinearMap.smul_apply, ← map_smul] at h0
    rw [← Submodule.Quotient.mk_eq_zero]
    exact h0

end Formalism.MainNotions.UnusedSlot80.UGen
end
