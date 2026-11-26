module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WeightCongruences.ExistsUnitEqRootOfUnityMulConjPhaseOne
section -- merged from Development.AutomorphicArithmetic.WeightCongruences.RootOfUnityGaloisActionCMDatum
open NumberField Formalism.HC

theorem UpperTheory.rootOfUnity_galois_action_CMDatum :
    ∀ (φ : Frame) (H : HostAx φ) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      H.gal.symm φ.iod z = z ∧ H.conj z = z⁻¹ ∧ H.gal.symm φ.sg z = z⁻¹ := by
  intro φ H z hz
  have C : HostCore H.toHostRaw := { H.der with }
  have h1 : H.gal.symm φ.iod z = z :=
    Der.kc_iod_fix H.toHostRaw C _ (H.gal.apply_symm_apply _) z hz
  have h2 : H.conj z = z⁻¹ :=
    eq_inv_of_mul_eq_one_right (Der.kc_conj_mul_self H.toHostRaw C z hz)
  refine ⟨h1, h2, ?_⟩
  rw [← φ.cc_mul_iod, map_mul, AlgEquiv.mul_apply, h1]
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.WeightCongruences.ProdCmTypePhaseOneAddRootOfUnity
open NumberField IsDedekindDomain Formalism.BasicNotions

private theorem prod_pair {G : Type*} [Group G] [Fintype G] {M : Type*} [CommMonoid M]
    (s : G) (hs1 : s ≠ 1) (hs2 : s * s = 1) (f : G → M) (hf : ∀ g, f g * f (g * s) = 1) :
    ∏ g, f g = 1 := by
  refine Finset.prod_involution (fun g _ => g * s) (fun g _ => hf g) ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro g _ _ h
    apply hs1
    simpa using h
  · intro g _
    rw [mul_assoc, hs2, mul_one]

private theorem phase_pair (w : ℂ) (m : ℕ) (hm : 0 < m) (hw : w ^ m = 1) (hz : 1 + w ≠ 0) :
    (1 + w) / ((‖1 + w‖ : ℝ) : ℂ) * ((1 + w⁻¹) / ((‖1 + w⁻¹‖ : ℝ) : ℂ)) = 1 := by
  have hn : ‖w‖ = 1 := by
    have h := congrArg (‖·‖) hw
    simp only [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hm.ne').1 h
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    have : Complex.normSq w = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn, one_pow]
    rw [Complex.inv_def, this, inv_one, Complex.ofReal_one, mul_one]
  have hconj : 1 + w⁻¹ = (starRingEnd ℂ) (1 + w) := by
    rw [hinv, map_add (f := _), map_one]
  rw [hconj, Complex.norm_conj]
  set a := 1 + w with ha
  have hna : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  rw [div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem UpperTheory.prod_cmType_phase_one_add_rootOfUnity :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → z ≠ -1 →
      ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (1 + z) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (1 + z)‖ : ℝ) : ℂ)) = 1 := by
  intro R H ι _ eT z hz hzne
  letI : Fintype R.Psi := Fintype.ofEquiv ι eT
  set F : R.Psi → ℂ := fun p =>
    H.emb (p : R.GG) (1 + z) / ((‖H.emb (p : R.GG) (1 + z)‖ : ℝ) : ℂ) with hF
  change ∏ τ, F (eT τ) = 1
  rw [Equiv.prod_comp eT F]
  obtain ⟨m, hm, hzm⟩ := hz
  have hsg := (UpperTheory.rootOfUnity_galois_action_CMDatum R.toFrame H.toHostAx z ⟨m, hm, hzm⟩).2.2
  refine prod_pair ⟨R.sg, R.sg_mem_Psi⟩ ?_ ?_ F ?_
  · intro h
    exact R.sg_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext R.sg_mul_sg
  · intro g
    have hz1 : 1 + z ≠ 0 := by
      intro h
      apply hzne
      linear_combination h
    have key : H.emb ((g * ⟨R.sg, R.sg_mem_Psi⟩ : R.Psi) : R.GG) (1 + z)
        = 1 + (H.emb (g : R.GG) z)⁻¹ := by
      simp only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, Subgroup.coe_mul, map_mul,
        RingHom.comp_apply]
      change H.φ₀ ((H.gal.symm (g : R.GG) * H.gal.symm R.sg) (1 + z))
        = 1 + (H.φ₀ ((H.gal.symm (g : R.GG)) z))⁻¹
      rw [AlgEquiv.mul_apply, map_add (f := _), map_one, hsg, map_add (f := _), map_one, map_inv₀, map_add (f := _),
        map_one, map_inv₀]
    have hne : 1 + H.emb (g : R.GG) z ≠ 0 := by
      have : H.emb (g : R.GG) (1 + z) ≠ 0 := (map_ne_zero _).2 hz1
      simpa using this
    simp only [hF, key]
    have e1 : H.emb (g : R.GG) (1 + z) = 1 + H.emb (g : R.GG) z := by simp
    rw [e1]
    exact phase_pair _ m hm (by rw [← map_pow, hzm, map_one]) hne
end

open NumberField IsDedekindDomain Formalism.BasicNotions

private theorem emb_sqd {R : Ranks} (H : Host R) (g : R.Psi) :
    H.emb (g : R.GG) H.sqd = Complex.I * (Real.sqrt H.d : ℂ) := by
  have hfix : (H.gal.symm (g : R.GG)) H.sqd = H.sqd := by
    have := (Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx (H.gal.symm (g : R.GG))).1
    apply this
    simp [Formalism.HC.HostRaw.galE]
  have h0 := H.φ₀_mem
  simp only [Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq] at h0
  simp only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, RingHom.comp_apply]
  change H.φ₀ ((H.gal.symm (g : R.GG)) H.sqd) = _
  rw [hfix, h0]

private theorem four_dvd {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : 4 ∣ Nat.card φ.Psi := by
  rw [Formalism.HC.Frame.natCard_Psi]
  have h1 : 4 ∣ 2 ^ φ.e := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.pow_dvd_pow 2 H.two_le_e
  exact Dvd.dvd.mul_left (h1.trans φ.two_pow_dvd_ord) 2

private theorem val_sqrt {L : Type} [Field L] [NumberField L] (d : ℕ) (δ : L) (h : δ ^ 2 = -(d : L))
    (P : HeightOneSpectrum (𝓞 L)) (hP : ((d : ℕ) : 𝓞 L) ∉ P.asIdeal) : P.valuation L δ = 1 := by
  have hd : P.valuation L (d : L) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 L) L) d, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact hP
  have h2 : P.valuation L δ ^ 2 = 1 := by
    rw [← map_pow, h, Valuation.map_neg, hd]
  exact sq_eq_one.mp h2

private theorem val_one_add {L : Type} [Field L] [NumberField L] (N : ℕ) (hN : Even N) (hN0 : 0 < N) (z : L)
    (hz : z ^ N = 1) (hne : z ≠ -1) (P : HeightOneSpectrum (𝓞 L)) (hP : ((N : ℕ) : 𝓞 L) ∉ P.asIdeal) :
    P.valuation L (1 + z) = 1 := by
  have hint : IsIntegral ℤ z := by
    refine ⟨Polynomial.X ^ N - 1, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C 1 hN0.ne'
    · simp [hz]
  set zi : 𝓞 L := ⟨z, hint⟩ with hzi
  have hcoe : algebraMap (𝓞 L) L zi = z := rfl
  have hzi1 : zi ^ N = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hcoe, hz, map_one]
  have hm1 : (-1 : 𝓞 L) ^ N = 1 := hN.neg_one_pow
  have hmem : (1 + zi) ∉ P.asIdeal := by
    intro h
    apply hne
    have : zi = -1 := by
      refine Formalism.HC.Der.kc_eq_of_pow_eq_one P.asIdeal hP hzi1 hm1 ?_
      simpa [sub_neg_eq_add, add_comm] using h
    have := congrArg (algebraMap (𝓞 L) L) this
    rwa [hcoe, map_neg, map_one] at this
  have : (1 + z : L) = algebraMap (𝓞 L) L (1 + zi) := by
    rw [map_add (f := _), map_one, hcoe]
  rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
  exact hmem

theorem UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      ∃ δ : (H.E)ˣ, (δ : H.E) = z * H.conj (δ : H.E) ∧
        (∀ P : HeightOneSpectrum (𝓞 H.E), ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal → P.valuation H.E (δ : H.E) = 1) ∧
        ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E)‖ : ℝ) : ℂ)) = 1 := by
  intro R H ι _ eT z hz
  by_cases hne : z = -1
  · subst hne
    have hs : H.sqd ≠ 0 := H.sqd_ne_zero
    refine ⟨Units.mk0 H.sqd hs, ?_, ?_, ?_⟩
    · have hc : H.conj H.sqd = -H.sqd := H.conj_sqd
      rw [Units.val_mk0, hc]
      ring
    · intro P hP
      refine val_sqrt H.d _ H.sqd_sq P fun hm => hP ?_
      obtain ⟨k, hk⟩ := H.d_dvd_condN
      rw [hk, Nat.cast_mul]
      exact P.asIdeal.mul_mem_right _ hm
    · have hd : 0 < H.d := H.hyp.2.1.pos
      have hr : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
      have ht : ∀ g : R.Psi, H.emb (g : R.GG) H.sqd / ((‖H.emb (g : R.GG) H.sqd‖ : ℝ) : ℂ) = Complex.I := fun g => by
        rw [emb_sqd H g, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hr.le, mul_div_assoc, div_self (by exact_mod_cast hr.ne'), mul_one]
      simp only [Units.val_mk0, ht]
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_congr eT]
      obtain ⟨k, hk⟩ : 4 ∣ Nat.card R.Psi := four_dvd H.toHostRaw
      rw [hk, pow_mul, Complex.I_pow_four, one_pow]
  · have hδ : 1 + z ≠ 0 := fun h0 => hne (by linear_combination h0)
    have hconj : H.conj z = z⁻¹ := (UpperTheory.rootOfUnity_galois_action_CMDatum _ H.toHostAx z hz).2.1
    have hz0 : z ≠ 0 := UpperTheory.root_ne_zero hz
    refine ⟨Units.mk0 (1 + z) hδ, ?_, ?_, ?_⟩
    · rw [Units.val_mk0, map_add (f := _), map_one, hconj]
      field_simp
      ring
    · intro P hP
      have hw : z ^ H.toHostRaw.w = 1 := (H.toHostRaw.isMu_iff z).1 hz
      obtain ⟨k, hk⟩ := H.toHostRaw.w_dvd_condN
      have hN : z ^ H.condN = 1 := by rw [hk, pow_mul, hw, one_pow]
      exact val_one_add H.condN (even_iff_two_dvd.2 H.two_dvd_condN) (Nat.pos_of_ne_zero H.condN_ne_zero) z hN hne P hP
    · exact UpperTheory.prod_cmType_phase_one_add_rootOfUnity R H ι eT z hz hne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEta
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEta
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf EtaTExists embPsi
open GlobalTheory.Mem.Chr.IdlFact

namespace GlobalTheory.Mem.EtaExt

def freeHom {X G : Type} [CommGroup G] (g : X → G) : Multiplicative (X →₀ ℤ) →* G where
  toFun m := (Multiplicative.toAdd m).prod fun v z => g v ^ z
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul]
    exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

theorem freeHom_apply {X G : Type} [CommGroup G] (g : X → G) (m : X →₀ ℤ) :
    freeHom g (Multiplicative.ofAdd m) = ∏ v ∈ m.support, g v ^ m v := rfl

theorem freeHom_single {X G : Type} [CommGroup G] (g : X → G) (v : X) (z : ℤ) :
    freeHom g (Multiplicative.ofAdd (Finsupp.single v z)) = g v ^ z :=
  Finsupp.prod_single_index (h := fun v z => g v ^ z) (zpow_zero _)

theorem freeHom_eq_finprod {X G : Type} [CommGroup G] (g : X → G) (m : X →₀ ℤ) :
    freeHom g (Multiplicative.ofAdd m) = ∏ᶠ v, g v ^ m v := by
  rw [freeHom_apply, finprod_eq_prod_of_mulSupport_subset]
  intro v hv
  by_contra h
  have : m v = 0 := by simpa using h
  exact hv (by simp [this])

variable {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

private theorem ordF_unif_self' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ordF w (unif w) = 1 := ordF_unif_self w

theorem valuation_eq_exp (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    P.valuation L (k : L) = WithZero.exp (-ordF P k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

theorem ordF_mul (P : HeightOneSpectrum (𝓞 L)) (k k' : Lˣ) : ordF P (k * k') = ordF P k + ordF P k' := by
  have h := valuation_eq_exp P (k * k')
  rw [Units.val_mul, map_mul, valuation_eq_exp, valuation_eq_exp, ← WithZero.exp_add, WithZero.exp_inj] at h
  omega

theorem valAt_diag (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    valAt P (diagUnits L k) = WithZero.exp (-ordF P k) := by
  rw [← valuation_eq_exp]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _

theorem mem_aboveF (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 L)) :
    Q ∈ aboveF (L := L) F v ↔ Q.under (𝓞 F) = v := by
  unfold aboveF; rw [Set.Finite.mem_toFinset]; rfl

open Classical in
theorem valAt_locF (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    valAt P (locF F v k) = WithZero.exp (-(if P.under (𝓞 F) = v then ordF v k else 0)) := by
  unfold locF
  rw [map_prod]
  change ∏ Q ∈ aboveF (L := L) F v, valAt P (localIdele L Q (atFin Q (upF F k))) = _
  split_ifs with hw
  · rw [Finset.prod_eq_single P (fun Q _ hQ => valAt_localIdele_ne hQ.symm _)
      (fun h => absurd ((mem_aboveF v P).2 hw) h), valAt_localIdele_self, ← hw, ← hord, ← valuation_eq_exp]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  · rw [neg_zero, WithZero.exp_zero]
    refine Finset.prod_eq_one fun Q hQ => valAt_localIdele_ne ?_ _
    rintro rfl
    exact hw ((mem_aboveF _ _).1 hQ)

theorem valAt_free (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 L)) (m : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    valAt P (freeHom (fun v => locF (L := L) F v (unif v)) (Multiplicative.ofAdd m)) =
      WithZero.exp (-m (P.under (𝓞 F))) := by
  classical
  rw [freeHom_apply, map_prod, Finset.prod_eq_single (P.under (𝓞 F))]
  · rw [map_zpow, valAt_locF hord, if_pos rfl, ordF_unif_self', ← WithZero.exp_zsmul]
    simp
  · intro v _ hv
    rw [map_zpow, valAt_locF hord, if_neg hv.symm]
    simp
  · intro h
    have : m (P.under (𝓞 F)) = 0 := by simpa using h
    rw [this, zpow_zero, map_one]

theorem exists_under (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 L), P.under (𝓞 F) = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, HeightOneSpectrum.ext hl.over.symm⟩
  exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q

theorem comap_bijective {c : L ≃ₐ[F] L} {I : Type} {φ : I → L →+* ℂ} (h : CMData F c φ) :
    Function.Bijective fun w : InfinitePlace L => w.comap (algebraMap F L) := by
  have := h.real
  have := h.cplx
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨InfinitePlace.comap_surjective (k := F) (K := L), ?_⟩
  have h1 := IsTotallyComplex.finrank L
  have h2 := IsTotallyReal.finrank F
  have h3 := Module.finrank_mul_finrank ℚ F L
  rw [h.rank] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyReal.nrComplexPlaces_eq_zero F]
  omega

theorem sign_zpow_odd {x : ℝ} (hx : x ≠ 0) {n : ℤ} (hn : Odd n) :
    ((x : ℂ) / ((‖(x : ℂ)‖ : ℝ) : ℂ)) ^ n = if x < 0 then -1 else 1 := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_neg h]
    push_cast
    rw [div_neg, div_self hx', hn.neg_one_zpow]
  · rw [abs_of_nonneg (not_lt.1 h), div_self hx', one_zpow]

theorem etaInf_eq [IsTotallyReal F] (ψ : L →+* ℂ) {n : ℤ} (hn : Odd n) (k : Fˣ) :
    ((etaInf F ((InfinitePlace.mk ψ).comap (algebraMap F L)) k : ℂˣ) : ℂ) =
      (ψ (upF F k : Lˣ) / ((‖ψ (upF F k : Lˣ)‖ : ℝ) : ℂ)) ^ n := by
  have hr : ComplexEmbedding.IsReal (ψ.comp (algebraMap F L)) :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  have e : ψ (upF F k : Lˣ) = ((hr.embedding (k : F) : ℝ) : ℂ) := (hr.coe_embedding_apply (k : F)).symm
  unfold etaInf
  rw [InfinitePlace.comap_mk, InfinitePlace.embedding_mk_eq_of_isReal hr, e, sign_zpow_odd (by simp) hn,
    ← hr.coe_embedding_apply, Complex.ofReal_re]
  split_ifs <;> simp

theorem prod_etaInf {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) {n : I → ℤ}
    (hn : ∀ i, Odd (n i)) (k : Fˣ) :
    ((∏ w : InfinitePlace F, etaInf F w k : ℂˣ) : ℂ) =
      ∏ i, (φ i (upF F k : Lˣ) / ((‖φ i (upF F k : Lˣ)‖ : ℝ) : ℂ)) ^ n i := by
  have := h.real
  rw [Units.coe_prod]
  symm
  refine Fintype.prod_bijective _ ((comap_bijective h).comp h.bij) _ _ fun i => ?_
  exact (etaInf_eq (φ i) (hn i) k).symm

theorem conj_conj {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) (x : L) :
    c (c x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
  apply w.embedding.injective
  rw [h.embedding_conj, h.embedding_conj, Complex.conj_conj]

theorem exists_upF {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) (k : Lˣ)
    (hk : c (k : L) = k) : ∃ a : Fˣ, upF F a = k := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := h.rank }
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h.rank]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (k : L)).2 fun σ => by
    by_cases e : σ = 1
    · rw [e]; rfl
    · rw [(hy σ e).trans (hy c h.ne).symm, hk]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← ha, map_zero])
  exact ⟨Units.mk0 a ha0, Units.ext ha⟩

theorem div_conj_isRoot {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) (k : Lˣ)
    (m : HeightOneSpectrum (𝓞 F) → ℤ) (hk : ∀ P : HeightOneSpectrum (𝓞 L), ordF P k = m (P.under (𝓞 F))) :
    ∃ r : ℕ, 0 < r ∧ ((k : L) / c k) ^ r = 1 := by
  have hk0 : (k : L) ≠ 0 := k.ne_zero
  have hc0 : c (k : L) ≠ 0 := by simp
  have h1 := normOne_unit_isRoot F L c I φ h (Units.mk0 (k / c k) (div_ne_zero hk0 hc0)) (by
    rw [Units.val_mk0, map_div₀, conj_conj h]; field_simp) (fun P => by
    obtain ⟨P', hP, -⟩ := existsUnique_conjPl c.toRingEquiv P
    have hu := (under_eq_iff_conjPl c h.rank h.ne P P').2 (Or.inr hP)
    have h2 : P'.valuation L (c (c k)) = P.valuation L (c k) := hP (c k)
    rw [conj_conj h] at h2
    rw [Units.val_mk0, map_div₀, ← h2, valuation_eq_exp, valuation_eq_exp, hk, hk, hu]
    exact div_self WithZero.exp_ne_zero)
  rwa [Units.val_mk0] at h1

theorem etaFin_unif_zpow (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    etaFin (L := L) F v (unif v) ^ ordF v k = etaFin (L := L) F v k := by
  unfold etaFin
  split_ifs
  · rw [ordF_unif_self', zpow_one]
  · rw [one_zpow]

theorem cmHeckeChar_ideleCompat_finprod {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ)
    (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (hprod : ∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) *
      ∏ w : InfinitePlace F, etaInf F w a = 1)
    {n : I → ℤ} (hn : ∀ i, Odd (n i)) (δ : Lˣ)
    (hδ : ∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ))
    (hδ' : ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) (a : Fˣ)
    (m : HeightOneSpectrum (𝓞 F) → ℤ)
    (hk : ∀ P : HeightOneSpectrum (𝓞 L), ordF P (δ * upF F a) = -m (P.under (𝓞 F))) :
    ((∏ᶠ v, etaFin (L := L) F v (unif v) ^ m v : ℂˣ) : ℂ) =
      ∏ i, (φ i (δ * upF F a : Lˣ) / ((‖φ i (δ * upF F a : Lˣ)‖ : ℝ) : ℂ)) ^ n i := by
  have e1 : ∀ v, etaFin (L := L) F v (unif v) ^ m v = (etaFin (L := L) F v a)⁻¹ := fun v => by
    obtain ⟨P, rfl⟩ := exists_under (L := L) v
    have h1 := hk P
    rw [ordF_mul, hord] at h1
    unfold etaFin
    split_ifs with hc
    · obtain ⟨r, hr⟩ := hδ P hc
      have : m (P.under (𝓞 F)) = 2 * (-r) + -ordF (P.under (𝓞 F)) a := by omega
      rw [ordF_unif_self', zpow_one, this, zpow_add, zpow_neg, zpow_mul]
      simp [zpow_ofNat]
    · simp
  simp only [e1]
  rw [finprod_inv_distrib, inv_eq_of_mul_eq_one_right (hprod a), prod_etaInf h hn, ← one_mul (∏ i, _), ← hδ',
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← mul_zpow, Units.val_mul, map_mul, norm_mul]
  push_cast
  rw [mul_div_mul_comm]

theorem compat {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ)
    (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (hprod : ∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) *
      ∏ w : InfinitePlace F, etaInf F w a = 1)
    {n : I → ℤ} (hn : ∀ i, Odd (n i))
    (hroot : ∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧
      (∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ)) ∧
      ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) (k : Lˣ)
    (m : HeightOneSpectrum (𝓞 F) → ℤ)
    (hk : ∀ P : HeightOneSpectrum (𝓞 L), ordF P k = -m (P.under (𝓞 F))) :
    ((∏ᶠ v, etaFin (L := L) F v (unif v) ^ m v : ℂˣ) : ℂ) =
      ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i := by
  obtain ⟨δ, hδe, hδ, hδ'⟩ := hroot _ (div_conj_isRoot h k (fun v => -m v) hk)
  have hk0 : (k : L) ≠ 0 := k.ne_zero
  have hck : c (k : L) ≠ 0 := by simp
  have hδ0 : (δ : L) ≠ 0 := δ.ne_zero
  have hcδ : c (δ : L) ≠ 0 := by simp
  have e : (δ : L) * c (k : L) = k * c (δ : L) := by
    calc (δ : L) * c (k : L) = (k / c k * c δ) * c (k : L) := by rw [← hδe]
      _ = k * c (δ : L) := by field_simp
  obtain ⟨a, ha⟩ := exists_upF h (δ⁻¹ * k) (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
    linear_combination e)
  obtain rfl : k = δ * upF F a := by rw [ha, mul_inv_cancel_left]
  exact cmHeckeChar_ideleCompat_finprod h hord hprod hn δ hδ hδ' a m hk

theorem infIdele_mem (w : InfinitePlace L) (y : (w.Completion)ˣ) : infIdele L w y ∈ unitIdl L := fun v => by
  show Valued.v (1 : v.adicCompletion L) = 1
  exact map_one _

theorem infDiag_eq (k : Lˣ) : infDiag k = ∏ w, infIdele L w (atInf w k) := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply]; rfl


open Classical in
theorem exists_unramified_resEta : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → (∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k) → (∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) * ∏ w : InfinitePlace F, etaInf F w a = 1) → ∀ (n : I → ℤ), (∀ i, Odd (n i)) → (∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧ (∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ)) ∧ ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ (∀ v, χ.UnrAt v) ∧ χ.ResEta F ∧ χ.HasInf φ n := by
  intro F L _ _ _ _ _ c I _ φ h hord hprod n hn hroot
  have := h.real
  obtain ⟨ψ, hψc, hψu, hψi, -, hψl, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar L I φ h.bij n ∅ (fun _ => 1) (by simp)
  have hψl' : ∀ v x, ψ (localIdele L v x) = 1 := fun v x => hψl v (by simp) x
  have hψF : ∀ v k, ψ (locF F v k) = 1 := fun v k => by
    unfold locF
    rw [map_prod]
    exact Finset.prod_eq_one fun Q _ => hψl' _ _
  have hψinf : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i := fun k => by
    rw [infDiag_eq, map_prod, Units.coe_prod]
    symm
    exact Fintype.prod_bijective _ h.bij _ _ fun i => (hψi i k).symm
  let β := freeHom fun v => locF (L := L) F v (unif v)
  let b := freeHom fun v => etaFin (L := L) F v (unif v)
  have hψβ : ∀ m, ψ (β m) = 1 := fun m => by
    show ψ (freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd m))) = 1
    rw [freeHom_apply, map_prod]
    exact Finset.prod_eq_one fun v _ => by rw [map_zpow, hψF, one_zpow]
  obtain ⟨χ, hχc, hχu, hχU, hχA⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles L)
    (Lˣ × Multiplicative (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (unitIdl L)
    (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open L).1 ((diagUnits L).coprod β) (MonoidHom.coprod 1 b) ψ hψc hψu
    (fun y => by
      show ‖((1 * freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd y.2)) : ℂˣ) : ℂ)‖ = 1
      rw [one_mul, freeHom_apply, Units.coe_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      unfold etaFin
      split_ifs <;> simp)
    (fun y hy => by
      obtain ⟨k, m⟩ := y
      show 1 * freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd m)) = ψ (diagUnits L k * β m)
      rw [one_mul, map_mul, hψβ, mul_one, hψd, Finset.prod_empty, mul_one, freeHom_eq_finprod]
      apply Units.ext
      rw [hψinf]
      refine compat h hord hprod hn hroot k _ fun P => ?_
      have h1 : valAt P (diagUnits L k * freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd m))) = 1 := hy P
      rw [map_mul, valAt_diag, valAt_free hord, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h1
      omega)
  have hχd : ∀ k : Lˣ, χ (diagUnits L k) = 1 := fun k => by simpa using hχA (k, 1)
  have hχβ : ∀ m, χ (β m) = b m := fun m => by simpa using hχA (1, m)
  refine ⟨⟨χ, hχc, hχd⟩, hχu, fun v x hx => ?_, ⟨fun v k => ?_, fun w k => ?_⟩, fun k => ?_⟩
  · show χ (localIdele L v x) = 1
    rw [hχU _ fun w => ?_, hψl']
    show valAt w _ = 1
    by_cases e : w = v
    · subst e; rw [valAt_localIdele_self]; exact hx
    · exact valAt_localIdele_ne e x
  · have e : Chr.HChar.resFin ⟨χ, hχc, hχd⟩ v k = χ (locF F v k) := by
      rw [Chr.HChar.resFin_apply]
      unfold locF
      rw [map_prod]
      rfl
    have h1 := hχβ (Multiplicative.ofAdd (Finsupp.single v (ordF v k)))
    have h2 := hχU (locF F v k * (β (Multiplicative.ofAdd (Finsupp.single v (ordF v k))))⁻¹) fun P => by
      show valAt P _ = 1
      rw [map_mul, map_inv, valAt_locF hord, valAt_free hord, Finsupp.single_apply]
      simp only [eq_comm (a := v)]
      exact mul_inv_cancel₀ WithZero.exp_ne_zero
    rw [map_mul, map_mul, map_inv, map_inv, hψF, hψβ, inv_one, mul_one, mul_inv_eq_one, h1] at h2
    rw [e, h2, freeHom_single, etaFin_unif_zpow]
  · obtain ⟨i, rfl⟩ := ((comap_bijective h).comp h.bij).2 w
    have e : aboveInf (L := L) F ((InfinitePlace.mk (φ i)).comap (algebraMap F L)) = {InfinitePlace.mk (φ i)} := by
      ext w'
      simp only [aboveInf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact (comap_bijective h).1.eq_iff
    show Chr.HChar.resInf _ ((InfinitePlace.mk (φ i)).comap (algebraMap F L)) k =
      etaInf F ((InfinitePlace.mk (φ i)).comap (algebraMap F L)) k
    rw [Chr.HChar.resInf_apply, e, Finset.prod_singleton]
    apply Units.ext
    rw [etaInf_eq (φ i) (hn i), ← hψi, ← hχU _ (infIdele_mem _ _)]
    rfl
  · rw [← hψinf, ← hχU _ (by rw [infDiag_eq]; exact prod_mem fun w _ => infIdele_mem _ _)]
    rfl

end GlobalTheory.Mem.EtaExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEtaStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf EtaTExists embPsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_resEta_alt : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → (∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k) → (∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) * ∏ w : InfinitePlace F, etaInf F w a = 1) → ∀ (n : I → ℤ), (∀ i, Odd (n i)) → (∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧ (∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ)) ∧ ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ (∀ v, χ.UnrAt v) ∧ χ.ResEta F ∧ χ.HasInf φ n := by
  first | exact @GlobalTheory.Mem.EtaExt.exists_unramified_resEta | exact GlobalTheory.Mem.EtaExt.exists_unramified_resEta | (intros; apply GlobalTheory.Mem.EtaExt.exists_unramified_resEta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf EtaTExists embPsi

namespace GlobalTheory.Mem.EtaT

theorem card_above {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (v : HeightOneSpectrum (𝓞 F)) :
    (aboveF (L := L) F v).card = (Ideal.primesOver v.asIdeal (𝓞 L)).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _
    (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  simp only [aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, rfl, rfl⟩
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      HeightOneSpectrum.ext h2.over.symm, rfl⟩

private theorem card_above_of_prime {R : Ranks} (H : Formalism.BasicNotions.Host R) (l : ℕ) (hp : l.Prime) (hl : l ∣ H.condN)
    (P : HeightOneSpectrum (𝓞 H.E)) (hP : ((l : ℕ) : 𝓞 H.E) ∈ P.asIdeal) :
    (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 2 := by
  have : Fact l.Prime := ⟨hp⟩
  have hPp := P.isPrime
  have hPZ : P.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hP
  have he := H.der.eta.2.2 l hl P.asIdeal
  change (if (Ideal.primesOver (P.under (𝓞 H.F)).asIdeal (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
  rw [card_above]
  by_contra hc
  rw [if_neg hc] at he
  exact absurd he (by decide)

private theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (N : ℕ) (hN : N ≠ 0)
    (h : (N : A) ∈ P) : ∃ l : ℕ, l.Prime ∧ l ∣ N ∧ (l : A) ∈ P := by
  induction N using induction_on_primes with
  | zero => exact absurd rfl hN
  | one => exact absurd (P.eq_top_iff_one.2 (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨l, h1, h2, h3⟩ := ih (fun h0 => hN (by rw [h0, mul_zero])) h
      exact ⟨l, h1, h2.mul_left _, h3⟩


open Classical in
theorem etaT_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  intro R H
  obtain ⟨c, hc, hcm, hunr, -, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unramified_resEta_alt H.F H.E c (R.Psi) (embPsi H) hcm hunr (GlobalTheory.T.quadraticChar_product_formula_CM_host R H)
    (fun _ => 1) (fun _ => odd_one) (fun ζ hζ => by
      obtain ⟨δ, hδ, hval, hprod⟩ := UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one R H R.Psi (Equiv.refl _) ζ hζ
      refine ⟨δ, by rw [hc]; exact hδ, fun P hP => ?_, ?_⟩
      · have hn : ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal := fun hm => by
          obtain ⟨l, hl, hlN, hlP⟩ := exists_prime_mem P.asIdeal P.isPrime H.condN H.condN_ne_zero hm
          rw [card_above_of_prime H l hl hlN P hlP] at hP
          exact absurd hP (by decide)
        have h0 : ordF P δ = 0 := by simp [ordF, hval P hn]
        rw [h0]
        exact Even.zero
      · simp only [zpow_one]
        exact hprod)
  exact ⟨χ, h1, h2, h3, h4⟩

end GlobalTheory.Mem.EtaT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExistsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf EtaTExists embPsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_etaTilde_character_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  first | exact @GlobalTheory.Mem.EtaT.etaT_exists | exact GlobalTheory.Mem.EtaT.etaT_exists | (intros; apply GlobalTheory.Mem.EtaT.etaT_exists <;> assumption)
end
