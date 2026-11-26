module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

def latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) : Subring (Formalism.Per6.BdRp l) :=
  Subring.closure (Set.range (wB l) ∪ (rB l) '' {x | x ∈ K' ∧ IsIntegral ℤ_[l] x})

theorem wB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) (a : Wl l) :
    wB l a ∈ latS K' :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem rB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) {x : Om l}
    (hx : x ∈ K') (hi : IsIntegral ℤ_[l] x) : rB l x ∈ latS K' :=
  Subring.subset_closure (Or.inr ⟨x, ⟨hx, hi⟩, rfl⟩)

theorem ker_thB_eq {l : ℕ} [Fact l.Prime] :
    RingHom.ker (thB l) = IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) :=
  (GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm

end GlobalTheory.CompanionTheory.LTPer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExists
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.TopNil

theorem exists_thB_wB {l : ℕ} [Fact l.Prime] (y : ℂ_[l]) (hy : ‖y‖ ≤ 1) :
    ∃ a, thB l (wB l a) = y := by
  obtain ⟨a, ha⟩ := GroundTheory.PAdicHodge.IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l
    ⟨y, GroundTheory.PAdicHodge.mem_normInteger.2 hy⟩
  refine ⟨a, ?_⟩
  have h := GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus
    (K := ℂ_[l]) l a
  rw [ha] at h
  exact h

theorem near_tch_pow {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (hS : ∀ a, wB l a ∈ S)
    (ϖ : Formalism.Per6.BdRp l) (hϖ : thB l ϖ ≠ 0) (x : Tl l) (hx : ‖thB l (tch l x)‖ < 1) :
    ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) := by
  set c : ℂ_[l] := thB l (tch l x) with hc
  have hpos : 0 < ‖thB l ϖ‖ := norm_pos_iff.2 hϖ
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hx
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  have hle : ‖c‖ ^ (N + 1) ≤ ‖thB l ϖ‖ := by
    rw [pow_succ]
    calc ‖c‖ ^ N * ‖c‖ ≤ ‖c‖ ^ N * 1 :=
          mul_le_mul_of_nonneg_left hx.le (pow_nonneg (norm_nonneg _) _)
      _ = ‖c‖ ^ N := mul_one _
      _ ≤ ‖thB l ϖ‖ := hN.le
  have hy : ‖c ^ (N + 1) / thB l ϖ‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one hpos]
    exact hle
  obtain ⟨a, ha⟩ := exists_thB_wB _ hy
  refine ⟨wB l a, hS a, ?_⟩
  rw [pow_one, FB, pow_one, RingHom.mem_ker, map_sub, map_pow, map_mul, ha, ← hc]
  field_simp
  simp

theorem main : ∀ {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)), (∀ a, wB l a ∈ S) →
    ∀ (ϖ : Formalism.Per6.BdRp l), thB l ϖ ≠ 0 → ∀ x : Tl l, ‖thB l (tch l x)‖ < 1 →
      ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) :=
  fun S hS ϖ hϖ x hx => near_tch_pow S hS ϖ hϖ x hx

end GlobalTheory.CompanionTheory.LTPer.TopNil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExistsStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_near_power_exists : ∀ {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)), (∀ a, wB l a ∈ S) → ∀ (ϖ : Formalism.Per6.BdRp l),
    thB l ϖ ≠ 0 → ∀ x : Tl l, ‖thB l (tch l x)‖ < 1 → ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.TopNil.main | exact GlobalTheory.CompanionTheory.LTPer.TopNil.main | (intros; apply GlobalTheory.CompanionTheory.LTPer.TopNil.main <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidue
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidue
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem uniformiser_facts : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    2 ≤ qOf π ∧ l ∣ qOf π ∧ π ∣ (l : ↥(OL K)) ∧
      ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 ∧ ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
  intro l _ K π hπ
  obtain ⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l K
  have hlp : l.Prime := Fact.out
  have hi : Algebra.IsIntegral ℤ_[l] ↥(OL K) := integralClosure.algebraIsIntegral
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K)) := by
    intro a b hab
    have h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b := congrArg Subtype.val hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b] at h1
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)
  have hf : FaithfulSMul ℤ_[l] ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) :=
    (algebraMap_isIntegral_iff.mpr hi).isLocalHom hinj
  have hl : ¬ IsUnit ((l : ℕ) : ↥(OL K)) := by
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] ↥(OL K))] at hu
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)
  have hdvd : π ∣ ((l : ℕ) : ↥(OL K)) := by
    have hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K) := hl
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π} := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π}) := by
    have := hfin 1
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have hnt : Nontrivial (↥(OL K) ⧸ Ideal.span {π}) := by
    refine Ideal.Quotient.nontrivial_iff.2 ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hπ.not_isUnit
  have h2 : 2 ≤ qOf π := Finite.one_lt_card
  have hord : addOrderOf (1 : ↥(OL K) ⧸ Ideal.span {π}) = l := by
    have h1 : (1 : ↥(OL K) ⧸ Ideal.span {π}) ≠ 0 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), Ne, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
    refine addOrderOf_eq_prime ?_ h1
    rw [nsmul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {π})),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hq : l ∣ qOf π := by
    have := addOrderOf_dvd_natCard (1 : ↥(OL K) ⧸ Ideal.span {π})
    rwa [hord] at this
  have hl0 : ((l : ℕ) : ↥(OL K)) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) h
    simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
    exact hlp.ne_zero (by exact_mod_cast h2)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hπ
  have he : e ≠ 0 := by
    rintro rfl
    apply hl
    rw [pow_zero] at hu
    exact IsUnit.of_mul_eq_one _ hu
  have hnorm : ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
    intro μ
    rw [PadicComplex.norm_extends]
    have hint : ∀ x : ↥(OL K), ‖μ (x : ↥K.1)‖ ≤ 1 := by
      intro x
      rw [← GlobalTheory.isIntegral_padicInt_iff_norm_le_one]
      exact (x.2 : IsIntegral ℤ_[l] (x : ↥K.1)).map (μ.restrictScalars ℤ_[l])
    have hpow : (π : ↥K.1) ^ e = (l : ↥K.1) * ((u : ↥(OL K)) : ↥K.1) := by
      have := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) hu
      simpa using this.symm
    have h3 : ‖μ (π : ↥K.1)‖ ^ e < 1 := by
      rw [← norm_pow, ← map_pow, hpow, map_mul, norm_mul, map_natCast,
        ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) Padic.norm_p_lt_one (hint _)
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 h3
  exact ⟨h2, hq, hdvd, hnorm K.1.val, hnorm⟩

end GlobalTheory.CompanionTheory.LTPer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidueStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_properties_residue : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    2 ≤ qOf π ∧ l ∣ qOf π ∧ π ∣ (l : ↥(OL K)) ∧
      ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 ∧ ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.uniformiser_facts | exact GlobalTheory.CompanionTheory.LTPer.uniformiser_facts | (intros; apply GlobalTheory.CompanionTheory.LTPer.uniformiser_facts <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateLimitKernelZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateLimitKernelZero
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem theta_period_eq_zero_of_theta_eq_zero :
    ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q, θ Q = 0 → ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → θ t = 0 := by
  intro B _ S F ϖ C _ _ ϖ' hϖ θ hker hS hlt q hq Q hQ t ht
  have hy : ∀ n, θ (ltIter ϖ q n Q) = 0 := by
    intro n
    induction n with
    | zero => simpa [ltIter] using hQ
    | succ n ih =>
      have hs : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + (ltIter ϖ q n Q) ^ q := by
        simp only [ltIter, Function.iterate_succ_apply']
      rw [hs, map_add (f := _), map_mul, map_pow, ih]
      simp [show q ≠ 0 by omega]
  have hne : θ ϖ ≠ 0 := by
    intro h0
    have h1 : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := ht 1
  have hbound : ∀ m : ℕ, ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ ‖θ ϖ‖ ^ m := by
    intro m
    obtain ⟨N, hN⟩ := hc m
    obtain ⟨s, hsS, hs⟩ := hN N le_rfl
    have h0 := (hker _).mpr hs
    simp only [map_sub, map_mul, map_pow, hy, mul_zero, zero_sub] at h0
    have h1 : θ ϖ ^ c * θ t = -(θ ϖ ^ m * θ s) := by linear_combination -h0
    have h2 : ‖θ ϖ‖ ^ c * ‖θ t‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
      have := congrArg norm h1
      simpa [norm_mul, norm_pow, norm_neg] using this
    rw [h2]
    exact mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hsS)
  have hlim : Filter.Tendsto (fun m : ℕ => ‖θ ϖ‖ ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hapos.le hlt
  have hle : ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ 0 := ge_of_tendsto' hlim hbound
  have hz : ‖θ t‖ ≤ 0 := by
    by_contra hcon
    have : 0 < ‖θ ϖ‖ ^ c * ‖θ t‖ := mul_pos (pow_pos hapos c) (not_le.mp hcon)
    linarith
  exact norm_le_zero_iff.mp hz

end GlobalTheory.CompanionTheory.LTPer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateLimitKernelZeroStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_limit_kernel_zero : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q, θ Q = 0 → ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → θ t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.theta_period_eq_zero_of_theta_eq_zero | exact GlobalTheory.CompanionTheory.LTPer.theta_period_eq_zero_of_theta_eq_zero | (intros; apply GlobalTheory.CompanionTheory.LTPer.theta_period_eq_zero_of_theta_eq_zero <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterValuesIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterValuesIntegral
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.IntVal

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (z : Om l) (h : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hz : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  rw [← PadicAlgCl.spectralNorm_eq] at h
  unfold spectralNorm at h
  rw [spectralValue_le_one_iff (minpoly.monic hz)] at h
  have hlift : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hz)
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Om l), ← eval₂_map, hq, ← aeval_def]
  exact minpoly.aeval ℚ_[l] z

theorem mem_OL_of_norm_le_one (K : FinExt l) (x : ↥K.1) (h : ‖((x : ↥K.1) : Om l)‖ ≤ 1) :
    x ∈ OL K := by
  change x ∈ integralClosure ℤ_[l] ↥K.1
  rw [mem_integralClosure_iff]
  haveI : IsScalarTower ℤ_[l] ↥K.1 (Om l) := IsScalarTower.of_algebraMap_eq fun z => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l),
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1]
    rfl
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℤ_[l] ↥K.1 (Om l)) :=
    (algebraMap ↥K.1 (Om l)).injective
  exact (isIntegral_algHom_iff _ hinj).1 (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  have := K.2
  exact isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K.1).isCompact

theorem norm_le_one (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l))) (g : ↥(GK K)) :
    ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ≤ 1 := by
  haveI := compactSpace_GK K
  obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hpow : ∀ n : ℕ, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ^ n ≤ M := fun n => by
    have := hM _ ⟨g ^ n, rfl⟩
    simpa [map_pow, norm_pow] using this
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
  exact absurd (hpow n) (not_le.2 hn)

theorem integral_values {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) :
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ g, ∃ a : ↥(OL K), (a : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) := fun hc g =>
  ⟨⟨_, mem_OL_of_norm_le_one K _ (norm_le_one K χ hc g)⟩, rfl⟩

end GlobalTheory.CompanionTheory.LTPer.IntVal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterValuesIntegralStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_values_integral : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ g, ∃ a : ↥(OL K), (a : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.IntVal.integral_values | exact GlobalTheory.CompanionTheory.LTPer.IntVal.integral_values | (intros; apply GlobalTheory.CompanionTheory.LTPer.IntVal.integral_values <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationAeEqConvolution
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationAeEqConvolution
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem mol_ae_lConv : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ,
      (fun y : G n => Mol μ φ (⇑x) y.val) =ᵐ[μ] lConv μ V φ x := by
  intro n _ _ μ _ V _ _ _ hU φ hφ x
  obtain ⟨h1, h2⟩ := hU n μ
  have hφc : Continuous φ := hφ.1.continuous
  have hφv : Continuous (fun y : G n => φ y.val) := hφc.comp Units.continuous_val

  have hcont : Continuous (fun y : G n => φ y.val • lT μ V y x) :=
    hφv.smul (GlobalTheory.T.regular_representation_continuous n μ V hU x).2
  have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine ((GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff
      ?_).2 hφ.2.1
    intro g hg
    have hd : g.det ≠ 0 := hφ.2.2 hg
    have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hd)
    exact ⟨hu.unit, rfl⟩
  have hcs : HasCompactSupport (fun y : G n => φ y.val • lT μ V y x) := by
    refine HasCompactSupport.intro hK fun y hy => ?_
    have : φ y.val = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have hint : Integrable (fun y : G n => φ y.val • lT μ V y x) μ :=
    hcont.integrable_of_hasCompactSupport hcs

  have hmul : Measurable (fun p : G n × G n => p.1⁻¹ * p.2) :=
    (continuous_fst.inv.mul continuous_snd).measurable
  have hF : AEStronglyMeasurable
      (Function.uncurry fun (y z : G n) => φ y.val • (x : G n → V) (y⁻¹ * z)) (μ.prod μ) := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    have a1 : StronglyMeasurable (fun p : G n × G n => φ p.1.val) :=
      (hφv.comp continuous_fst).stronglyMeasurable
    have a2 : StronglyMeasurable (fun p : G n × G n => (x : G n → V) (p.1⁻¹ * p.2)) :=
      (Lp.stronglyMeasurable x).comp_measurable hmul
    exact a1.smul a2
  have hae : ∀ᵐ y ∂μ, (φ y.val • lT μ V y x : Lp V 2 μ) =ᵐ[μ]
      fun z => φ y.val • (x : G n → V) (y⁻¹ * z) := by
    refine Eventually.of_forall fun y => ?_
    filter_upwards [Lp.coeFn_smul (φ y.val) (lT μ V y x), lT_coe μ y x] with z e1 e2
    rw [e1, Pi.smul_apply, e2]
  have key := GlobalTheory.T.lp_integral_ae_pointwise (G n) (G n) V μ μ (fun y : G n => φ y.val • lT μ V y x)
    (fun y z => φ y.val • (x : G n → V) (y⁻¹ * z)) hint hF hae
  have hconv : lConv μ V φ x = ∫ y : G n, φ y.val • lT μ V y x ∂μ := rfl
  rw [hconv]
  filter_upwards [key] with z hz
  rw [hz]

  let H : G n → V := fun u => φ (z.val * (u⁻¹ : G n).val) • (x : G n → V) u
  have e2 : ∫ u, H u ∂μ = ∫ u, H (u⁻¹ * z) ∂μ := by
    rw [integral_inv_eq_self (fun u => H (u * z)) μ, integral_mul_right_eq_self H z]
  show ∫ u, H u ∂μ = _
  rw [e2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e3 : z.val * ((y⁻¹ * z)⁻¹ : G n).val = y.val := by
    rw [← Units.val_mul]
    congr 1
    group
  show φ (z.val * ((y⁻¹ * z)⁻¹ : G n).val) • (x : G n → V) (y⁻¹ * z) = _
  rw [e3]

end GlobalTheory.CompanionTheory.PresSobA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationAeEqConvolutionStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollification_ae_eq_convolution : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ, (fun y : G n => Mol μ φ (⇑x) y.val) =ᵐ[μ] lConv μ V φ x := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv | exact GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv | (intros; apply GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateLimitCongruence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateLimitCongruence
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.QLim

theorem map_mem {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) (q : ℕ) {x : B}
    (hx : x ∈ S) : ϖ * x + x ^ q ∈ S :=
  S.add_mem (S.mul_mem hϖ hx) (S.pow_mem hx q)

theorem step_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) {a b c : B} (hb : b ∈ S) (hc : c ∈ S) {m : ℕ} (hm : 1 ≤ m)
    (hab : a - b = ϖ ^ m * c) :
    ∃ c' ∈ S, (ϖ * a + a ^ q) - (ϖ * b + b ^ q) = ϖ ^ (m + 1) * c' := by
  obtain ⟨s, hs, hqs⟩ := hq
  have hy : ϖ ^ m * c ∈ S := S.mul_mem (S.pow_mem hϖ m) hc
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Polynomial.X ^ q : Polynomial S)
    (⟨b, hb⟩ : S) (⟨ϖ ^ m * c, hy⟩ : S)
  have hk' : (b + ϖ ^ m * c) ^ q =
      b ^ q + (q : B) * b ^ (q - 1) * (ϖ ^ m * c) + (k : B) * (ϖ ^ m * c) ^ 2 := by
    have h := congrArg (Subtype.val) hk
    simpa [Polynomial.derivative_X_pow] using h
  have ha : a = b + ϖ ^ m * c := by linear_combination hab
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨c + s * b ^ (q - 1) * c + (k : B) * ϖ ^ m' * c ^ 2, ?_, ?_⟩
  · exact S.add_mem (S.add_mem hc (S.mul_mem (S.mul_mem hs (S.pow_mem hb _)) hc))
      (S.mul_mem (S.mul_mem k.2 (S.pow_mem hϖ _)) (S.pow_mem hc _))
  · rw [ha, hk', hqs]; ring

theorem iter_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) (n : ℕ) :
    ∀ {a b c : B} {m : ℕ}, a ∈ S → b ∈ S → c ∈ S → 1 ≤ m → a - b = ϖ ^ m * c →
      ∃ c' ∈ S, ltIter ϖ q n a - ltIter ϖ q n b = ϖ ^ (m + n) * c' := by
  induction n with
  | zero =>
    intro a b c m _ _ hc _ hab
    exact ⟨c, hc, by simpa [ltIter] using hab⟩
  | succ n ih =>
    intro a b c m ha hb hc hm hab
    obtain ⟨c₁, hc₁, h₁⟩ := step_congr hϖ hq hb hc hm hab
    obtain ⟨c₂, hc₂, h₂⟩ := ih (map_mem hϖ q ha) (map_mem hϖ q hb) hc₁ (by omega) h₁
    refine ⟨c₂, hc₂, ?_⟩
    have e : m + (n + 1) = m + 1 + n := by omega
    rw [e]
    exact h₂

theorem exists_limit : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → (∀ n, v (n + 1) ^ q = v n) →
      ∃ Q ∈ S, ∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a := by
  intro B _ S F ϖ E q _ hq v hv hvq
  have hd : ∀ n, ∃ e ∈ S, ltIter ϖ q (n + 1) (v (n + 1)) - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * e := by
    intro n
    have h1 : (ϖ * v (n + 1) + v (n + 1) ^ q) - v n = ϖ ^ 1 * v (n + 1) := by
      rw [hvq]; ring
    obtain ⟨c, hc, h⟩ := iter_congr E.mem hq n (map_mem E.mem q (hv (n + 1))) (hv n) (hv (n + 1))
      le_rfl h1
    refine ⟨c, hc, ?_⟩
    have e : ltIter ϖ q (n + 1) (v (n + 1)) = ltIter ϖ q n (ϖ * v (n + 1) + v (n + 1) ^ q) := rfl
    rw [e, h, add_comm n 1]
  choose e he hde using hd
  let s : ℕ → B := fun n => Nat.casesOn n (v 0) e
  have hs : ∀ n, s n ∈ S := by
    intro n
    cases n with
    | zero => exact hv 0
    | succ n => exact he n
  obtain ⟨r, hr, hsum⟩ := E.sumS s hs
  have tel : ∀ N, ∑ n ∈ Finset.range (N + 1), ϖ ^ n * s n = ltIter ϖ q N (v N) := by
    intro N
    induction N with
    | zero => simp [s, ltIter]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hN : s (N + 1) = e N := rfl
      rw [hN, ← hde N]
      ring
  refine ⟨r, hr, fun n => ?_⟩
  obtain ⟨a, ha, h⟩ := hsum (n + 1)
  rw [tel n] at h
  exact ⟨a, ha, h⟩

end GlobalTheory.CompanionTheory.LTPer.QLim
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateLimitCongruenceStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_iterate_limit_congruence : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → (∀ n, v (n + 1) ^ q = v n) →
      ∃ Q ∈ S, ∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.QLim.exists_limit | exact GlobalTheory.CompanionTheory.LTPer.QLim.exists_limit | (intros; apply GlobalTheory.CompanionTheory.LTPer.QLim.exists_limit <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateDerivativeIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateDerivativeIntegral
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.IntForm

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem Rd_continuousOn {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContinuousOn (Rd X f) (GLs n) :=
  (GlobalTheory.CompanionTheory.SobGL.Smooth.contDiffOn_fderiv_apply' (GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n) hf
    (GlobalTheory.CompanionTheory.SobGL.Smooth.mulRight' X).contDiff.contDiffOn).continuousOn

theorem hasDerivAt_curve {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) (z : G n) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (z.val * (expC X r).val)) (Rd X f (z.val * (expC X s).val)) s := by
  have hγ := (GlobalTheory.T.matrix_exp_curve_derivative n X).2 s
  let L : CLof (Mat n) (Mat n) := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ z.val)
  have h1 : HasDerivAt (fun r : ℝ => z.val * (expC X r).val) (z.val * ((expC X s).val * X)) s :=
    L.hasFDerivAt.comp_hasDerivAt s hγ
  have hw : (z.val * (expC X s).val) ∈ GLs n := val_mem_GLs (z * expC X s)
  have h2 : HasFDerivAt f (fderiv ℝ f (z.val * (expC X s).val)) (z.val * (expC X s).val) :=
    ((hf.contDiffAt ((GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n).mem_nhds hw)).differentiableAt
      (by simp)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt s h1
  have e : z.val * ((expC X s).val * X) = (z.val * (expC X s).val) * X := (Matrix.mul_assoc _ _ _).symm
  rw [e] at h3
  exact h3

theorem continuous_F {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    Continuous (fun p : ℝ × G n => Rd X f (p.2.val * (expC X p.1).val)) := by
  have hc : Continuous (fun p : ℝ × G n => p.2 * expC X p.1) :=
    continuous_snd.mul ((GlobalTheory.T.matrix_exp_curve_derivative n X).1.comp continuous_fst)
  have hv : Continuous (fun p : ℝ × G n => (p.2 * expC X p.1).val) := Units.continuous_val.comp hc
  exact (Rd_continuousOn hf X).comp_continuous hv (fun p => val_mem_GLs (p.2 * expC X p.1))

section L2

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rR_cls_ae (hU : Unimod) {g : Mat n → V} (hg : MemLp (fun y : G n => g y.val) 2 μ) (h : G n) :
    rR μ V h (cls μ g) =ᵐ[μ] fun z => g (z.val * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have h1 := hm.quasiMeasurePreserving.ae_eq_comp (coe_cls μ hg)
  filter_upwards [rR_coe μ hU h (cls μ g), h1] with z hz1 hz2
  rw [hz1]
  simpa using hz2

theorem setIntegral_ae (hU : Unimod) {f : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : MemLp (fun y : G n => Rd X f y.val) 2 μ) (a b : ℝ) :
    (⇑(∫ s in Set.Ioc a b, rR μ V (expC X s) (cls μ (Rd X f))) : G n → V) =ᵐ[μ]
      fun z => ∫ s in Set.Ioc a b, Rd X f (z.val * (expC X s).val) := by
  have hc : Continuous (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f))) :=
    ((GlobalTheory.T.regular_representation_continuous n μ V hU (cls μ (Rd X f))).1).comp (GlobalTheory.T.matrix_exp_curve_derivative n X).1
  have hint : Integrable (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f)))
      (volume.restrict (Set.Ioc a b)) := hc.integrableOn_Ioc
  refine GlobalTheory.T.lp_integral_ae_pointwise ℝ (G n) V (volume.restrict (Set.Ioc a b)) μ _
    (fun s z => Rd X f (z.val * (expC X s).val)) hint ?_ ?_
  · have : Continuous (Function.uncurry fun (s : ℝ) (z : G n) => Rd X f (z.val * (expC X s).val)) :=
      continuous_F hf X
    exact this.aestronglyMeasurable
  · exact ae_of_all _ fun s => rR_cls_ae μ hU hg (expC X s)

end L2

theorem rR_sub_cls_eq_integral : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (f : Mat n → V) (X : Mat n), ContDiffOn ℝ ∞ f (GLs n) → MemLp (fun y : G n => f y.val) 2 μ → MemLp (fun y : G n => Rd X f y.val) 2 μ → ∀ t : ℝ, rR μ V (expC X t) (cls μ f) - cls μ f = ∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f)) := by
  intro n _ _ μ _ V _ _ _ hU f X hf hfm hg t
  apply Lp.ext
  rw [intervalIntegral]
  have hsub1 := Lp.coeFn_sub (rR μ V (expC X t) (cls μ f)) (cls μ f)
  have hsub2 := Lp.coeFn_sub (∫ s in Set.Ioc 0 t, rR μ V (expC X s) (cls μ (Rd X f)))
    (∫ s in Set.Ioc t 0, rR μ V (expC X s) (cls μ (Rd X f)))
  filter_upwards [hsub1, hsub2, rR_cls_ae μ hU hfm (expC X t), coe_cls μ hfm,
    setIntegral_ae μ hU X hf hg 0 t, setIntegral_ae μ hU X hf hg t 0] with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, h6]
  have hcont : Continuous (fun s : ℝ => Rd X f (z.val * (expC X s).val)) :=
    (continuous_F hf X).comp (Continuous.prodMk continuous_id continuous_const)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (f := fun r : ℝ => f (z.val * (expC X r).val))
    (f' := fun s : ℝ => Rd X f (z.val * (expC X s).val))
    (fun s _ => hasDerivAt_curve hf X z s) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral] at key
  rw [key]
  simp [expC_zero]

end GlobalTheory.CompanionTheory.PresSobA.IntForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateDerivativeIntegralStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translate_derivative_integral : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (f : Mat n → V) (X : Mat n), ContDiffOn ℝ ∞ f (GLs n) → MemLp (fun y : G n => f y.val) 2 μ → MemLp (fun y : G n => Rd X f y.val) 2 μ → ∀ t : ℝ, rR μ V (expC X t) (cls μ f) - cls μ f = ∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f)) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.IntForm.rR_sub_cls_eq_integral | exact GlobalTheory.CompanionTheory.PresSobA.IntForm.rR_sub_cls_eq_integral | (intros; apply GlobalTheory.CompanionTheory.PresSobA.IntForm.rR_sub_cls_eq_integral <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTorsionApproximation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTorsionApproximation
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

section ThQ

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem thq_add_le {x y : C} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem thq_pow_sub (b d : C) (hb : ‖b‖ ≤ 1) (hbd : ‖b + d‖ ≤ 1) (m : ℕ) :
    ∃ e : C, ‖e‖ ≤ ‖d‖ ∧ (b + d) ^ (m + 1) - b ^ (m + 1) = d * (((m + 1 : ℕ) : C) * b ^ m + e) := by
  induction m with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨e, he, h⟩ := ih
    refine ⟨d * ((m + 1 : ℕ) : C) * b ^ m + (b + d) * e, ?_, ?_⟩
    · apply thq_add_le
      · rw [norm_mul, norm_mul, norm_pow]
        have h1 : ‖((m + 1 : ℕ) : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C (m + 1)
        have h2 : ‖b‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
        calc ‖d‖ * ‖((m + 1 : ℕ) : C)‖ * ‖b‖ ^ m ≤ ‖d‖ * 1 * 1 := by gcongr
          _ = ‖d‖ := by ring
      · rw [norm_mul]
        calc ‖b + d‖ * ‖e‖ ≤ 1 * ‖d‖ := by gcongr
          _ = ‖d‖ := one_mul _
    · have h3 : (b + d) ^ (m + 1 + 1) - b ^ (m + 1 + 1)
          = (b + d) * ((b + d) ^ (m + 1) - b ^ (m + 1)) + d * b ^ (m + 1) := by ring
      rw [h3, h]
      push_cast
      ring

theorem thq_step {P : C} {q : ℕ} (hq : 2 ≤ q) (hqP : ‖(q : C)‖ ≤ ‖P‖) {a b : C}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {r : ℝ} (hab : ‖a - b‖ ≤ r) (hr : r ≤ ‖P‖) :
    ‖(P * a + a ^ q) - (P * b + b ^ q)‖ ≤ ‖P‖ * r := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hab
  obtain ⟨e, he, h⟩ := thq_pow_sub b (a - b) hb (by simpa using ha) m
  rw [add_sub_cancel] at h
  have h1 : (P * a + a ^ (m + 1)) - (P * b + b ^ (m + 1))
      = P * (a - b) + (a - b) * (((m + 1 : ℕ) : C) * b ^ m + e) := by
    rw [← h]; ring
  rw [h1]
  apply thq_add_le
  · rw [norm_mul]; gcongr
  · have h2 : ‖((m + 1 : ℕ) : C) * b ^ m + e‖ ≤ ‖P‖ := by
      apply thq_add_le
      · rw [norm_mul, norm_pow]
        have h3 : ‖b‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
        calc ‖((m + 1 : ℕ) : C)‖ * ‖b‖ ^ m ≤ ‖P‖ * 1 := by gcongr
          _ = ‖P‖ := mul_one _
      · exact he.trans (hab.trans hr)
    rw [norm_mul, mul_comm]
    gcongr

theorem thq_ball {P : C} {q : ℕ} (hP : ‖P‖ ≤ 1) {a : C} (ha : ‖a‖ ≤ 1) : ‖P * a + a ^ q‖ ≤ 1 := by
  apply thq_add_le
  · rw [norm_mul]
    calc ‖P‖ * ‖a‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul _
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem thq_iter {P : C} {q : ℕ} (hq : 2 ≤ q) (hqP : ‖(q : C)‖ ≤ ‖P‖) (hP : ‖P‖ ≤ 1) (n : ℕ) :
    ∀ (a b : C) (r : ℝ), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a - b‖ ≤ r → r ≤ ‖P‖ →
      ‖ltIter P q n a - ltIter P q n b‖ ≤ ‖P‖ ^ n * r := by
  induction n with
  | zero => intro a b r _ _ hab _; simpa [ltIter] using hab
  | succ n ih =>
    intro a b r ha hb hab hr
    have hr0 : 0 ≤ r := (norm_nonneg _).trans hab
    have h1 := thq_step hq hqP ha hb hab hr
    have h2 : ‖P‖ * r ≤ ‖P‖ := by
      calc ‖P‖ * r ≤ 1 * r := by gcongr
        _ = r := one_mul _
        _ ≤ ‖P‖ := hr
    have h3 := ih _ _ _ (thq_ball hP ha) (thq_ball hP hb) h1 h2
    have e1 : ∀ x : C, ltIter P q (n + 1) x = ltIter P q n (P * x + x ^ q) := fun x => by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, e1]
    calc _ ≤ ‖P‖ ^ n * (‖P‖ * r) := h3
      _ = ‖P‖ ^ (n + 1) * r := by ring

theorem thq_map {B : Type} [CommRing B] (θ : B →+* C) (ϖ : B) (q n : ℕ) (x : B) :
    θ (ltIter ϖ q n x) = ltIter (θ ϖ) q n (θ x) := by
  induction n generalizing x with
  | zero => simp [ltIter]
  | succ n ih =>
    have e1 : ltIter ϖ q (n + 1) x = ltIter ϖ q n (ϖ * x + x ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    have e2 : ltIter (θ ϖ) q (n + 1) (θ x) = ltIter (θ ϖ) q n (θ ϖ * θ x + θ x ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, e2, ih]
    simp

theorem thq_tower {P : C} {q : ℕ} {w : ℕ → C} (h0 : w 0 = 0)
    (hw : ∀ n, w (n + 1) ^ q + P * w (n + 1) = w n) (n : ℕ) : ltIter P q n (w n) = 0 := by
  induction n with
  | zero => simpa [ltIter] using h0
  | succ n ih =>
    have e1 : ltIter P q (n + 1) (w (n + 1)) = ltIter P q n (P * w (n + 1) + w (n + 1) ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, add_comm, hw, ih]

end ThQ

theorem theta_eq_zero_of_congr_torsion : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ →
    ∀ (θ : B →+* C), (∀ s ∈ S, ‖θ s‖ ≤ 1) → θ ϖ ≠ 0 → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q → ‖(q : C)‖ ≤ ‖θ ϖ‖ →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → ∀ (w : ℕ → C), w 0 = 0 → (∀ n, w (n + 1) ^ q + θ ϖ * w (n + 1) = w n) →
      (∀ n, ‖θ (v n) - w n‖ ≤ ‖θ ϖ‖) →
    ∀ Q ∈ S, (∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a) → θ Q = 0 := by
  intro B _ S F ϖ C _ _ _ θ hS _ hlt q hq hqP v hv w h0 hw hvw Q hQ hQn
  have hP : ‖θ ϖ‖ ≤ 1 := hlt.le
  have hwb : ∀ n, ‖w n‖ ≤ 1 := fun n => by
    have h1 : w n = θ (v n) + -(θ (v n) - w n) := by ring
    rw [h1]
    exact thq_add_le (hS _ (hv n)) (by rw [norm_neg]; exact (hvw n).trans hP)
  have hb : ∀ n, ‖θ Q‖ ≤ ‖θ ϖ‖ ^ (n + 1) := fun n => by
    obtain ⟨a, ha, hQa⟩ := hQn n
    have h1 : θ Q = ltIter (θ ϖ) q n (θ (v n)) + θ ϖ ^ (n + 1) * θ a := by
      have h2 : θ (Q - ltIter ϖ q n (v n)) = θ (ϖ ^ (n + 1) * a) := congrArg θ hQa
      rw [map_sub, thq_map, map_mul, map_pow] at h2
      rw [← h2]; ring
    have h3 := thq_iter hq hqP hP n (θ (v n)) (w n) _ (hS _ (hv n)) (hwb n) (hvw n) le_rfl
    rw [thq_tower h0 hw n, sub_zero] at h3
    rw [h1]
    apply thq_add_le
    · calc _ ≤ ‖θ ϖ‖ ^ n * ‖θ ϖ‖ := h3
        _ = ‖θ ϖ‖ ^ (n + 1) := by ring
    · rw [norm_mul, norm_pow]
      calc ‖θ ϖ‖ ^ (n + 1) * ‖θ a‖ ≤ ‖θ ϖ‖ ^ (n + 1) * 1 := by
            gcongr
            exact hS _ ha
        _ = ‖θ ϖ‖ ^ (n + 1) := mul_one _
  have hlim : Filter.Tendsto (fun n : ℕ => ‖θ ϖ‖ ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt).comp (Filter.tendsto_add_atTop_nat 1)
  have h0' : ‖θ Q‖ ≤ 0 := ge_of_tendsto' hlim hb
  exact norm_le_zero_iff.mp h0'

end GlobalTheory.CompanionTheory.LTPer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTorsionApproximationStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_torsion_approximation : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ →
    ∀ (θ : B →+* C), (∀ s ∈ S, ‖θ s‖ ≤ 1) → θ ϖ ≠ 0 → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q → ‖(q : C)‖ ≤ ‖θ ϖ‖ →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → ∀ (w : ℕ → C), w 0 = 0 → (∀ n, w (n + 1) ^ q + θ ϖ * w (n + 1) = w n) →
      (∀ n, ‖θ (v n) - w n‖ ≤ ‖θ ϖ‖) →
    ∀ Q ∈ S, (∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a) → θ Q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion | exact GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion | (intros; apply GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion <;> assumption)
end
end
end
