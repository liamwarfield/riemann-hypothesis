module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WeightCongruences.ProdCmTypeEqNormAndWeightCongruenceOne
open NumberField IsDedekindDomain Formalism.BasicNotions

private theorem fixK {R : Ranks} (H : Host R) (σ : H.E ≃ₐ[ℚ] H.E) (hσ : σ H.sqd = H.sqd) (x : H.K) :
    σ (x : H.E) = x := by
  have hint : IsAlgebraic ℚ H.sqd := (Algebra.IsIntegral.isIntegral (R := ℚ) H.sqd).isAlgebraic
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint]
    exact x.2
  have hle : Algebra.adjoin ℚ {H.sqd} ≤
      AlgHom.equalizer (σ : H.E →ₐ[ℚ] H.E) (AlgHom.id ℚ H.E) := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact hσ
  exact hle hx

private theorem sigma_sqd {R : Ranks} (H : Host R) (g : R.Psi) : H.sigmaOf (g : R.GG) H.sqd = H.sqd := by
  rw [← Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx]
  simpa [Formalism.BasicNotions.Host.sigmaOf, Formalism.HC.HostRaw.galE] using g.2

private noncomputable def galK {R : Ranks} (H : Host R) (g : R.Psi) : H.E ≃ₐ[H.K] H.E :=
  AlgEquiv.ofRingEquiv (f := (H.sigmaOf (g : R.GG)).toRingEquiv) (fun y => fixK H _ (sigma_sqd H g) y)

private theorem galK_bij {R : Ranks} (H : Host R) : Function.Bijective (galK H) := by
  constructor
  · intro g₁ g₂ h
    have h' : H.sigmaOf (g₁ : R.GG) = H.sigmaOf (g₂ : R.GG) := by
      ext y
      exact congrArg (fun f : H.E ≃ₐ[H.K] H.E => f y) h
    apply Subtype.ext
    simpa [Formalism.BasicNotions.Host.sigmaOf] using h'
  · intro τ
    have hτ : (τ.restrictScalars ℚ) H.sqd = H.sqd := by
      have := τ.commutes (⟨H.sqd, H.sqd_mem_K⟩ : H.K)
      simpa using this
    refine ⟨⟨H.gal (τ.restrictScalars ℚ), ?_⟩, ?_⟩
    · exact (Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx _).mpr hτ
    · ext y
      simp [galK, Formalism.BasicNotions.Host.sigmaOf]

theorem UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi),
      (∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x)) ∧
      UpperTheory.MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := by
  intro R H ι _ eT
  haveI : IsGalois ℚ H.E := H.galois
  haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  have hnorm : ∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x =
      algebraMap H.K H.E (Algebra.norm H.K x) := by
    intro x
    rw [Algebra.norm_eq_prod_automorphisms]
    exact Fintype.prod_bijective (fun τ => galK H (eT τ)) ((galK_bij H).comp eT.bijective)
      _ _ (fun τ => rfl)
  refine ⟨hnorm, ?_⟩
  intro z hz
  have h1 := hnorm z
  rw [H.der.norm_mu z hz, map_one] at h1
  simp only [zpow_one, Formalism.BasicNotions.Host.emb, RingHom.comp_apply, RingHom.coe_coe]
  rw [← map_prod, h1, map_one]
end

section -- merged from Development.AutomorphicArithmetic.WeightCongruences.ExistsShiftWeightCongruenceLtTorsionOrder
open NumberField IsDedekindDomain

theorem UpperTheory.exists_shift_weightCongruence_lt_torsionOrder :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (φ : ι → E →+* K) (e : ι → ℤ) (i₀ : ι),
      ∃ s : ℕ, s < NumberField.Units.torsionOrder E ∧ UpperTheory.MU φ (fun i => e i + if i = i₀ then (s : ℤ) else 0) := by
  intro E K _ _ _ ι _ _ φ e i₀
  obtain ⟨μ, hμ⟩ : ∃ μ : NumberField.Units.torsion E,
      orderOf μ = NumberField.Units.torsionOrder E :=
    IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers E) E)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : E, IsPrimitiveRoot ζ (NumberField.Units.torsionOrder E) := ⟨_, hμ⟩
  have hw0 : 0 < NumberField.Units.torsionOrder E := NumberField.Units.torsionOrder_pos E
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hw0.ne'
  have hψ : IsPrimitiveRoot (φ i₀ ζ) (NumberField.Units.torsionOrder E) :=
    hζ.map_of_injective (φ i₀).injective
  have hc0 : (∏ i, (φ i ζ) ^ e i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ((map_ne_zero _).mpr hζ0)
  have hcw : ((∏ i, (φ i ζ) ^ e i)⁻¹) ^ (NumberField.Units.torsionOrder E) = 1 := by
    rw [inv_pow, ← Finset.prod_pow]
    have h1 : ∀ i ∈ (Finset.univ : Finset ι),
        ((φ i ζ) ^ e i) ^ (NumberField.Units.torsionOrder E) = 1 := by
      intro i _
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow,
        hζ.pow_eq_one, map_one, one_zpow]
    rw [Finset.prod_eq_one h1, inv_one]
  obtain ⟨s, hs, hsc⟩ := hψ.eq_pow_of_pow_eq_one hcw
  refine ⟨s, hs, ?_⟩
  have key : ∏ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0) = 1 := by
    have hsplit : ∀ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0) =
        (φ i ζ) ^ e i * (if i = i₀ then (φ i ζ) ^ s else 1) := by
      intro i
      rw [zpow_add₀ ((map_ne_zero _).mpr hζ0)]
      split_ifs <;> simp
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _), hsc,
      mul_inv_cancel₀ hc0]
  intro z hz
  obtain ⟨m, hm, hzm⟩ := hz
  have hzw : z ^ (NumberField.Units.torsionOrder E) = 1 := by
    have hpos : 0 < orderOf z :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hzm⟩)
    haveI : NeZero (orderOf z) := ⟨hpos.ne'⟩
    obtain ⟨k, hk⟩ :=
      NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.orderOf z)
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hzw
  calc ∏ i, (φ i (ζ ^ j)) ^ (e i + if i = i₀ then (s : ℤ) else 0)
      = (∏ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0)) ^ j := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    _ = 1 := by rw [key, one_pow]
end

open NumberField Formalism.BasicNotions

namespace UpperTheory.Mu

variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (eT : ι ≃ R.Psi)

theorem mu_one : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := (UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one R H ι eT).2

theorem mu_const (c : ℤ) : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => c) := (mu_one H eT).const c

theorem prod_emb_zpow {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (c : ℤ) :
    ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z ^ c = 1 := mu_const H eT c z hz

theorem prod_emb {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z = 1 := by
  simpa using prod_emb_zpow H eT hz 1

theorem muq_of_parallel {a : ι → ℤ} (ha : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) a) {e : ι → ℚ} (c : ℤ)
    (he : ∀ τ, e τ = a τ + c) : MUQ (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) e :=
  ⟨fun τ => a τ + c, fun τ => by rw [he]; push_cast; rfl, ha.add_const (mu_one H eT) c⟩

theorem exists_shift [DecidableEq ι] (a : ι → ℤ) (τ₀ : ι) : ∃ s : ℕ, s < Units.torsionOrder H.E ∧
    MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun τ => a τ + if τ = τ₀ then (s : ℤ) else 0) :=
  UpperTheory.exists_shift_weightCongruence_lt_torsionOrder H.E ℂ ι _ a τ₀

end UpperTheory.Mu
