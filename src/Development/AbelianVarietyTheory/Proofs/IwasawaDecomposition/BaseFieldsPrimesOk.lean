module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
open Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem

namespace GlobalTheory.Mem.Col2

theorem fOk_of_fieldsOk {X : Fields} (hX : X.Ok) (σ : X.K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) :
    FOk X.emb σ :=
  ⟨hX.conjE, hX.emb_star, hσ⟩

theorem base_fOk (B : Base) : letI := B.fields.starE; FOk B.fields.emb B.embLL :=
  fOk_of_fieldsOk (GlobalTheory.Mem.FieldsLaws.fields_ok B) B.embLL B.starLL_cx

theorem base_fields_primes_ok : ∀ (B : Base) (X : PreX B.toPre),
    B.fields.Ok ∧ (B.primes X).Ok ∧ B.wts.Ok ∧ (letI := B.host.cmStar; FOk B.tauLL B.embLL) ∧
      2 * B.fields.f * B.R.k < (B.primes X).g 0 - 1 := fun B X =>
  ⟨GlobalTheory.Mem.FieldsLaws.fields_ok B, (GlobalTheory.BasePrimes.primes_ok B X).1,
    { row_ok τ := ⟨B.hc τ, rfl⟩
      hc_row u τ := by
        show RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ)
        unfold RowPar.of
        rw [B.hcW_v, B.hcW_b, B.hcW_e]
      u_first u u' τ h := (B.hcW_first u τ h).trans (B.hcW_first u' τ h).symm
      u_last u u' τ h := (B.hcW_last u τ (by omega)).trans (B.hcW_last u' τ (by omega)).symm },
    base_fOk B, by rw [B.fields_f]; exact X.g_big 0⟩

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E] {h : ℕ}

theorem one_mem_pow : (1 : E) ∈ powIdealElts E h :=
  ⟨one_ne_zero, 1, by rw [one_pow, FractionalIdeal.spanSingleton_one]⟩

theorem mul_mem_pow {x y : E} (hx : x ∈ powIdealElts E h) (hy : y ∈ powIdealElts E h) :
    x * y ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  obtain ⟨hy0, b, hb⟩ := hy
  exact ⟨mul_ne_zero hx0 hy0, a * b, by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ha, hb, mul_pow]⟩

theorem inv_mem_pow {x : E} (hx : x ∈ powIdealElts E h) : x⁻¹ ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  exact ⟨inv_ne_zero hx0, a⁻¹, by rw [← FractionalIdeal.spanSingleton_inv, ha, inv_pow]⟩

theorem npow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℕ) : x ^ n ∈ powIdealElts E h := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_pow
  | succ n ih => rw [pow_succ]; exact mul_mem_pow ih hx

theorem zpow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℤ) : x ^ n ∈ powIdealElts E h := by
  cases n with
  | ofNat n => simpa using npow_mem_pow hx n
  | negSucc n => rw [zpow_negSucc]; exact inv_mem_pow (npow_mem_pow hx _)

theorem prod_mem_pow {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ∈ powIdealElts E h) :
    ∏ i ∈ s, f i ∈ powIdealElts E h :=
  Finset.prod_induction f (· ∈ powIdealElts E h) (fun _ _ => mul_mem_pow) one_mem_pow hf

theorem map_mem_pow {E' : Type} [Field E'] [NumberField E'] (σ : E →+* E') {x : E} (hx : x ∈ powIdealElts E h) :
    σ x ∈ powIdealElts E' h := by
  obtain ⟨hx0, a, ha⟩ := hx
  have hle : (𝓞 E)⁰ ≤ Submonoid.comap (RingOfIntegers.mapRingHom σ) (𝓞 E')⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun a b hab =>
      RingOfIntegers.ext (σ.injective (congrArg (fun y : 𝓞 E' => (y : E')) hab))
  have hm : IsLocalization.map E' (RingOfIntegers.mapRingHom σ) hle = σ :=
    IsLocalization.ringHom_ext (𝓞 E)⁰ (by rw [IsLocalization.map_comp]; rfl)
  refine ⟨(map_ne_zero σ).2 hx0, FractionalIdeal.extendedHom' E' hle a, ?_⟩
  rw [← map_pow, ← ha]
  change _ = FractionalIdeal.extended E' _ _
  rw [FractionalIdeal.extended_spanSingleton, hm]

theorem exists_aut [IsGalois ℚ E] (φ τ : E →+* ℂ) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, τ x = φ (σ x) := by
  letI := φ.toAlgebra
  let t : E →ₐ[ℚ] ℂ := τ.toRatAlgHom
  exact ⟨t.restrictNormal' E, fun x => (t.restrictNormal_commutes E x).symm⟩

theorem exists_gen (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ γ : 𝓞 E, γ ≠ 0 ∧ 𝔞 ^ classNumber E = Ideal.span {γ} := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  have h1 : ClassGroup.mk0 (𝔠 ^ classNumber E) = 1 := by
    rw [map_pow, classNumber, pow_card_eq_one]
  obtain ⟨γ, hγ⟩ := (ClassGroup.mk0_eq_one_iff (𝔠 ^ classNumber E).2).1 h1
  have hγ' : 𝔞 ^ classNumber E = Ideal.span {γ} := hγ
  refine ⟨γ, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ h𝔞 hγ'

theorem span_eq_extend (K : IntermediateField ℚ ℂ) [NumberField K] (τ : E →+* ℂ) (hK : ∀ x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) : Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} =
      extendIdealHom (τ.codRestrict K hK) 𝔞 := by
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K hK) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

end GlobalTheory.Mem.FieldsEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
noncomputable section

namespace GlobalTheory.Mem.Col2.DiaStab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem tr_one (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp [GStep.tr, trFr_apply, frMul_one]

theorem evV_rho (b : S.β) (g : S.G b) (v : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem tr_mem (b : S.β) (g : S.G b)
    {F : Fr emb σ n → ℂ} (hF : F ∈ ValC (Gr emb σ n) lam) : S.tr emb σ b g F ∈ ValC (Gr emb σ n) lam := by
  rw [← span_evV emb 1 lam σ] at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [← evV_rho]
    exact evV_mem_ValC emb 1 lam σ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_Fi (hf : S.Free)
    (φ : S.Cl → Fr emb σ n → ℂ) (h : ∀ c, φ c ∈ ValC (Gr emb σ n) lam) : φ ∈ S.Fi emb σ lam := fun c =>
  ⟨h c, fun g => by rw [hf c.1 g.1 _ g.2, tr_one]⟩

end General

theorem lawDiaStable : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (_hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ h
  rintro P a _ ⟨φ, hφ, rfl⟩
  exact mem_Fi _ emb σ _ h.free0 _ fun c => tr_mem _ emb σ _ _ _ (hφ _).1

end GlobalTheory.Mem.Col2.DiaStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexFormsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_complexForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  first | exact @GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | exact GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | (intros; apply GlobalTheory.Mem.Col2.DiaStab.lawDiaStable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBound
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.PsiFix

end GlobalTheory.Mem.An.PsiFix

namespace GlobalTheory.Mem.An

end GlobalTheory.Mem.An
end

open Finset ArithmeticFunction Filter Topology

noncomputable section

namespace GlobalTheory.MangoldtSeries

theorem sum_not_coprime_le (q N : ℕ) (hq : q ≠ 0) :
    ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n ≤ Nat.log 2 N * Real.log q := by
  classical
  set S := (Icc 1 N).filter (fun n => ¬ n.Coprime q) with hS
  set L := Nat.log 2 N with hL
  have hT0 : ∀ p n : ℕ, 0 ≤ (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro p n; split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_rfl
  have hpt : ∀ n ∈ S, Λ n ≤ ∑ p ∈ q.primeFactors,
      (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hnc⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with hpp
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      have hmin : (p ^ k).minFac = p := by rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
      have hpq : p ∣ q := by
        by_contra h
        exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
      have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, hq⟩
      have hkL : k ∈ Icc 1 L := by
        rw [Finset.mem_Icc]
        refine ⟨hk, Nat.le_log_of_pow_le (by norm_num) ?_⟩
        exact (Nat.pow_le_pow_left hp.two_le k).trans hnN
      have hTp : (if p ^ k ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) = Real.log p :=
        if_pos (Finset.mem_image.2 ⟨k, hkL, rfl⟩)
      rw [hmin, ← hTp]
      exact Finset.single_le_sum (f := fun p' : ℕ => if p ^ k ∈ (Icc 1 L).image (p' ^ ·) then Real.log p' else 0)
        (fun p' _ => hT0 p' (p ^ k)) hpmem
    · exact Finset.sum_nonneg (fun p _ => hT0 p n)
  have hcard : ∀ p : ℕ, ((S ∩ (Icc 1 L).image (p ^ ·)).card : ℝ) ≤ L := by
    intro p
    have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := (Icc 1 L).image (p ^ ·)))
    have h2 := Finset.card_image_le (s := Icc 1 L) (f := (p ^ ·))
    have h3 : (Icc 1 L).card = L := by simp
    exact_mod_cast (h1.trans h2).trans h3.le
  calc ∑ n ∈ S, Λ n ≤ ∑ n ∈ S, ∑ p ∈ q.primeFactors,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ S,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, (L : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p _
        rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcard p) (Real.log_natCast_nonneg p)
    _ = (L : ℝ) * Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [← Finset.mul_sum, Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ (L : ℝ) * Real.log q := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.log_le_log
        · apply Finset.prod_pos
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q))

theorem norm_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
      ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
      Nat.log 2 N * Real.log q := by
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => ¬ n.Coprime q)]
  rw [Finset.sum_eq_zero (s := (Icc 1 N).filter (fun n => ¬¬ n.Coprime q)) ?_, add_zero]
  · calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q),
          ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
            ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter] at hn
          have hχ0 : χ (n : ZMod q) = 0 := by
            apply MulChar.map_nonunit
            rw [ZMod.isUnit_iff_coprime]
            exact hn.2
          rw [hχ0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          calc Λ n * ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ Λ n * 1 :=
                mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
                  ArithmeticFunction.vonMangoldt_nonneg
            _ = Λ n := mul_one _
      _ ≤ _ := sum_not_coprime_le q N (NeZero.ne q)
  · intro n hn
    rw [Finset.mem_filter, not_not] at hn
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn.2)
    push_cast at h
    rw [h, sub_self]

end GlobalTheory.MangoldtSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroSmulMemAlt
namespace GlobalTheory.NonzeroSmulMemIntegralSpan

theorem exists_ne_zero_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {M : Submodule (NumberField.RingOfIntegers K) V} {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : NumberField.RingOfIntegers K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hay
    · rw [mul_smul]; exact M.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj
      (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨a * q, mul_ne_zero ha (nonZeroDivisors.ne_zero q.2), ?_⟩
    have h1 : (q : NumberField.RingOfIntegers K) • c • y = p • y := by
      rw [← algebraMap_smul K (q : NumberField.RingOfIntegers K), smul_smul, mul_comm,
        ← algebraMap_smul K p y]
      exact congrArg (· • y) hpq
    rw [mul_smul, h1, smul_comm]
    exact M.smul_mem _ hay

end GlobalTheory.NonzeroSmulMemIntegralSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.LatGood

theorem map_mulVec_injective {K m k : Type} [Field K] [Fintype m] [Fintype k] (φ : K →+* ℂ) (B : Matrix m k K)
    (h : Function.Injective B.mulVec) : Function.Injective (B.map φ).mulVec := by
  classical
  have hk : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hk
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' B) = 1 := by
    rw [hg]; exact LinearMap.toMatrix'_id
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1
  have h2 : (LinearMap.toMatrix' g).map φ * B.map φ = 1 := by
    rw [← Matrix.map_mul, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  intro x y hxy
  have := congrArg ((LinearMap.toMatrix' g).map φ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h2] using this

section Datum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

def valMat (c : C.Cl) : Matrix C.ιV (Fin C.dim) K :=
  Matrix.of fun i a => C.bV.repr ((C.basis a : C.Cl → C.V) c) i

theorem pair_eq (x y : C.V) :
    C.pair x y = ∑ i, ∑ j, star (C.bV.repr x i) * C.gramV i j * C.bV.repr y j := by
  conv_lhs => rw [← C.bV.sum_repr x, ← C.bV.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, CSD.gramV, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_map (hb : C.HasRatBasis) (φ : K →+* ℂ) :
    C.H.map φ = ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ • (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pair_eq, Matrix.mul_apply, Matrix.conjTranspose_apply, valMat]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C.basis_rat hb a c i φ]
  rfl

theorem exists_val_ne (φ : K →+* ℂ) (x : Fin C.dim → ℂ) (hx : x ≠ 0) :
    ∃ c, ((valMat C c).map φ) *ᵥ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let B : Matrix (C.Cl × C.ιV) (Fin C.dim) K := Matrix.of fun p a => valMat C p.1 p.2 a
  have hB : Function.Injective B.mulVec := by
    intro u v huv
    apply C.I_injective
    funext c
    apply C.bV.repr.injective
    ext i
    have h1 := congrFun huv (c, i)
    simp only [Matrix.mulVec, dotProduct, B, valMat, Matrix.of_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CSD.I_eq_sum, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finsupp.smul_apply, smul_eq_mul]
    simpa only [mul_comm] using h1
  apply hx
  apply map_mulVec_injective φ B hB
  rw [Matrix.mulVec_zero]
  funext p
  exact congrFun (hcon p.1) p.2

theorem gram_posDef (hb : C.HasRatBasis) (φ : K →+* ℂ) (hp : (C.gramV.map φ).PosDef) : (C.H.map φ).PosDef := by
  have hw : ∀ c, (0 : ℂ) < ((C.wt c : ℕ) : ℂ)⁻¹ := fun c => inv_pos.mpr (by exact_mod_cast C.wt_pos c)
  rw [gram_map C hb φ]
  have hpsd : (∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ •
      (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ)).PosSemidef :=
    Matrix.posSemidef_sum _ fun c _ => (hp.posSemidef.conjTranspose_mul_mul_same _).smul (hw c).le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  have e : ∀ c, star x ⬝ᵥ (((C.wt c : ℕ) : ℂ)⁻¹ •
      (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ)) *ᵥ x =
      ((C.wt c : ℕ) : ℂ)⁻¹ * (star (((valMat C c).map φ) *ᵥ x) ⬝ᵥ (C.gramV.map φ) *ᵥ (((valMat C c).map φ) *ᵥ x)) := by
    intro c
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [e]
  obtain ⟨c, hc⟩ := exists_val_ne C φ x hx
  exact Finset.sum_pos' (fun c _ => mul_nonneg (hw c).le (hp.posSemidef.dotProduct_mulVec_nonneg _))
    ⟨c, Finset.mem_univ c, mul_pos (hw c) (hp.dotProduct_mulVec_pos hc)⟩


omit [StarRing K] in
theorem exists_smul_mem {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  exact _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem hx

theorem values_isLattice (M : C.Cl → Submodule (𝓞 K) C.V) (hM : ∀ c, Submodule.IsFullLattice K (M c))
    (L : Submodule (𝓞 K) C.Forms) (hL : ∀ x, x ∈ L ↔ ∀ c, x.1 c ∈ M c) :
    L.FG ∧ Submodule.span K (L : Set C.Forms) = ⊤ := by
  classical
  constructor
  · apply Submodule.fg_of_fg_map_injective (C.Forms.subtype.restrictScalars (𝓞 K)) Subtype.val_injective
    refine Submodule.FG.of_le (Submodule.fg_pi fun c => (hM c).fg) ?_
    rintro _ ⟨x, hx, rfl⟩ c _
    exact (hL x).1 hx c
  · apply eq_top_iff.mpr
    intro x _
    have hx : ∀ c, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x.1 c ∈ M c := fun c =>
      exists_smul_mem (by rw [(hM c).span_eq_top]; trivial)
    choose d hd hdx using hx
    let a : 𝓞 K := ∏ c, d c
    have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd c
    have hax : a • x ∈ L := (hL _).2 fun c => by
      change a • x.1 c ∈ M c
      dsimp [a]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), mul_smul]
      exact (M c).smul_mem _ (hdx c)
    have haK : algebraMap (𝓞 K) K a ≠ 0 := fun h =>
      ha ((IsFractionRing.injective (𝓞 K) K) (by simpa using h))
    have h := (Submodule.span K (L : Set C.Forms)).smul_mem
      (algebraMap (𝓞 K) K a)⁻¹ (Submodule.subset_span hax)
    rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ haK, one_smul] at h
    exact h
end Datum

theorem root_mem_cmMax {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) {u : K} {m : ℕ} (hm : m ≠ 0) (hu : u ^ m = 1) : u ∈ cmMax K := by
  have key : ∀ φ : K →+* ℂ, φ u⁻¹ = starRingEnd ℂ (φ u) := by
    intro φ
    have h1 : (φ u) ^ m = 1 := by rw [← map_pow, hu, map_one]
    rw [map_inv₀]
    exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hm)
  have hs : star u = u⁻¹ := σ.injective (by rw [hσ, key])
  intro φ
  rw [hs, key]

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem rho_rat (hF : FOk emb σ) (hS : S.Ok) (b : S.β) (g : S.G b) (i j : VVIdx lam) :
    (bVV K lam).repr (S.rho emb lam b g (bVV K lam j)) i ∈ cmMax K := by
  have he : ∀ τ x, emb τ x ∈ cmMax K := fun τ x φ => by
    rw [← hF.emb_star]
    exact hF.conjE (φ.comp (emb τ)) x
  have h1 := (GlobalTheory.coefAction_repr_mem_subfield emb (cmMax K) lam he (S.gam b g) i j).2
  obtain ⟨m, hm, hu⟩ := hS.root b g
  have h2 : ((S.chr b g : Kˣ) : K) ∈ cmMax K :=
    root_mem_cmMax σ hF.sig_star hm.ne' (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])
  have e : S.rho emb lam b g (bVV K lam j) = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) (bVV K lam j) := rfl
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem h2 h1

theorem hasRatBasis (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) : (S.csd emb lam h).HasRatBasis :=
  GlobalTheory.FormsDescent.hasRatBasis_of_act _ fun c γ i j => rho_rat S emb σ lam hF hS c.1 γ.1 i j

omit [StarRing E] in
theorem gramV_posDef (h : (S.fam emb lam).Ok) (φ : K →+* ℂ) : ((S.csd emb lam h).gramV.map φ).PosDef := by
  have h1 := pairingPositive_holds K ι n lam (gramKd emb (1 : Matrix (Fin n) (Fin n) E)) φ fun τ => by
    have : gramKd emb (1 : Matrix (Fin n) (Fin n) E) τ = 1 := by
      simp [gramKd]
    rw [this, map_one']
    exact Matrix.PosDef.one
  exact h1

theorem step_gram_posDef (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) (φ : K →+* ℂ) :
    ((S.csd emb lam h).H.map φ).PosDef :=
  gram_posDef _ (hasRatBasis S emb σ lam hF hS h) φ (gramV_posDef S emb lam h φ)

omit [StarRing K] in
theorem dualFr_isFullLattice {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (dualFr M) :=
  GlobalTheory.DualLat.isLattice_dualFr M hM

omit [StarRing E] [StarRing K] in
theorem delAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (delAtr emb lam L) :=
  (GlobalTheory.TransLattice.nabDelLattice K ι n lam _ fun τ =>
    dualFr_isFullLattice _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL)).2

theorem lawGood (hF : FOk emb σ) (hS : S.Ok)
    (hLsh : ∀ b (d : S.D b), Submodule.IsFullLattice E (S.Lsh b d))
    (h : (S.fam emb lam).Ok) : S.LawGood emb lam h := by
  exact ⟨fun v => (frameOfSpec _ _ (step_gram_posDef S emb σ lam hF hS h v.embedding)).1,
    values_isLattice (S.csd emb lam h) (fun c => delAtr emb lam (S.Lsh c.1 (S.rep c)))
      (fun c => delAtr_isLattice emb lam _ (hLsh c.1 (S.rep c))) _ fun _ => Iff.rfl⟩

end Step

end GlobalTheory.Mem.LatGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbeddingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_law_good_of_field_embedding : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF hS h
  exact GlobalTheory.Mem.LatGood.lawGood S emb σ lam hF hS hS.lsh_full_lat h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol.ScaleExists

theorem trueScale_isScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) :=
  GlobalTheory.Mem.Vol.Scale.cdScaleIs_trueScale

end GlobalTheory.Mem.Vol.ScaleExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulMemSpan
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.LevLaws

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


omit [StarRing E] in
theorem exists_mul_mem_span (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) : ∃ s ∉ P.asIdeal, ∀ r ∈ P.asIdeal, ∃ t, s * r = q * t := by
  have h1 : P.asIdeal ∣ Ideal.span {q} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨J, hJ⟩ := h1
  have h2 : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq2
    have : q ∈ P.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self q
    rw [sq]
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨s, hsP, fun r hr => ?_⟩
  have : r * s ∈ Ideal.span {q} := hJ ▸ Ideal.mul_mem_mul hr hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨t, by rw [mul_comm s r, ← ht, mul_comm]⟩

end Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

end GlobalTheory.Mem.Col2.LevLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumPosHerm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open scoped ComplexOrder

namespace GlobalTheory.Mem.Col2.ClassSumPos

theorem ipVal_pos {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (f : Fr emb σ n → ℂ) (hf : f ∈ ValC (Gr emb σ n) lam) (h0 : f ≠ 0) :
    0 < ipVal emb σ lam f f := by
  obtain ⟨P, -, rfl⟩ := hf
  have hP : P ≠ 0 := by
    rintro rfl
    exact h0 (map_zero _)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    show (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ = 1
    exact inv_one
  have h1 := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) P
  rw [e] at h1
  unfold ipVal
  rw [ipFr_apply, h1, ← nfL_apply]
  exact ps_nfL_pos lam P hP

theorem ipVal_herm {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (φ ψ : Fr emb σ n → ℂ) :
    ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  unfold ipVal
  rw [ipFr_apply, ipFr_apply, ← nfL_apply, ← nfL_apply, starRingEnd_apply, ps_nfL_symm]

theorem classSum_pos_herm : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ [Fintype S.Cl], (∀ φ ∈ S.Fi emb σ lam, φ ≠ 0 → 0 < (∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c)).re) ∧ ∀ φ ψ : Fr emb σ n → ℂ, ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam _ hS _
  refine ⟨fun φ hφ h0 => ?_, ipVal_herm emb σ lam⟩
  have hw : ∀ c : S.Cl, (0 : ℂ) < ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ := fun c => by
    haveI := hS.fin_stab c.1 (S.rep c)
    have hc : (0 : ℝ) < ((Nat.card (S.Stab c) : ℕ) : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
    have := Complex.zero_lt_real.2 hc
    simpa using this
  have hpos : (0 : ℂ) < ∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c) := by
    obtain ⟨c0, hc0⟩ := Function.ne_iff.1 h0
    refine Finset.sum_pos' (fun c _ => ?_) ⟨c0, Finset.mem_univ _, mul_pos (hw c0) (ipVal_pos emb σ lam _ (hφ c0).1 hc0)⟩
    by_cases h : φ c = 0
    · rw [h, map_zero, mul_zero]
    · exact (mul_pos (hw c) (ipVal_pos emb σ lam _ (hφ c).1 h)).le
  exact (Complex.lt_def.1 hpos).1

end GlobalTheory.Mem.Col2.ClassSumPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetAvg
open MeasureTheory

namespace GlobalTheory

open scoped Pointwise

theorem setIntegral_isFundamentalDomain_comp_mul_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have h2 : IsFundamentalDomain Γ (MulOpposite.op g • 𝓕) μ := h𝓕.smul_of_comm (MulOpposite.op g)
  have himg : MulOpposite.op g • 𝓕 = (fun x => x * g) '' 𝓕 := by
    ext y; simp [Set.mem_smul_set, MulOpposite.smul_eq_mul_unop]
    constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro hy; exact ⟨_, hy, by simp⟩
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) f 𝓕,
    ← himg]
  refine h2.setIntegral_eq h𝓕 ?_
  intro γ x
  rw [Subgroup.smul_def, smul_eq_mul]
  exact hf γ γ.2 x

theorem integral_fundamentalDomain_eq_sum_doubleCoset_avg : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → IsOpen (K : Set G) → μ K ≠ ⊤ → ∀ (U : Type) [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U] (ν : Measure U) [ν.IsMulLeftInvariant] [IsProbabilityMeasure ν] (j : U →* G), Continuous j → (∀ k ∈ K, ∃ k' ∈ Kf, ∃ w, k = k' * j w) → (∀ k ∈ Kf, ∀ w, k * j w = j w * k) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) → ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ k ∈ Kf, ∀ x, f (x * k) = f x) → IntegrableOn f 𝓕 μ ∧ ∫ x in 𝓕, f x ∂μ = ((μ K).toReal : ℂ) * ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * ∫ v, f (h i * j v) ∂ν := by
  intro G _ _ _ _ _ _ μ _ _ Γ K Kf _ 𝓕 h𝓕 hK hKfin U _ _ _ _ _ _ ν _ _ j hj hdec hcomm ι _ h huniq
    hfin f hf hfl hfr
  have key : ∀ x, ∀ k' ∈ Kf, ∀ w, f (x * (k' * j w)) = f (x * j w) := by
    intro x k' hk' w
    rw [hcomm k' hk' w, ← mul_assoc, hfr k' hk']
  have hbd : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hi : ∀ i, ∃ C, ∀ v, ‖f (h i * j v)‖ ≤ C := fun i =>
      (isCompact_range ((hf.comp (continuous_const.mul hj)).norm)).bddAbove.imp
        fun C hC v => hC ⟨v, rfl⟩
    choose B hB using hi
    refine ⟨∑ i, |B i|, fun x => ?_⟩
    obtain ⟨i, ⟨γ, hγ, k, hk, rfl⟩, -⟩ := huniq x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    rw [mul_assoc, hfl γ hγ, key _ k' hk' w]
    exact (hB i w).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨C, hC⟩ := hbd
  have hFl : ∀ γ ∈ Γ, ∀ x, ∫ v, f (γ * x * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro γ hγ x
    congr 1; funext v; rw [mul_assoc, hfl γ hγ]
  have hFr : ∀ k ∈ K, ∀ x, ∫ v, f (x * k * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro k hk x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    have e : ∀ v, f (x * (k' * j w) * j v) = f (x * j (w * v)) := by
      intro v
      have : x * (k' * j w) * j v = x * j (w * v) * k' := by
        calc x * (k' * j w) * j v = x * j w * (k' * j v) := by
                rw [hcomm k' hk' w]; simp only [mul_assoc]
          _ = x * j w * (j v * k') := by rw [hcomm k' hk' v]
          _ = x * j (w * v) * k' := by rw [map_mul]; simp only [mul_assoc]
      rw [this, hfr k' hk']
    simp_rw [e]
    exact integral_mul_left_eq_self (fun v => f (x * j v)) w
  obtain ⟨hfin𝓕, -, hFeq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G μ Γ K 𝓕 h𝓕 hK
    hKfin ι h huniq hfin (fun x => ∫ v, f (x * j v) ∂ν) hFl hFr
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin𝓕
  have hint : IntegrableOn f 𝓕 μ :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  refine ⟨hint, ?_⟩
  have hc : Continuous fun p : G × U => f (p.1 * j p.2) :=
    hf.comp (continuous_fst.mul (hj.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun x v => f (x * j v)) ((μ.restrict 𝓕).prod ν) :=
    Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hC _)
  calc ∫ x in 𝓕, f x ∂μ = ∫ x in 𝓕, ∫ v, f (x * j v) ∂ν ∂μ := by
        rw [integral_integral_swap hI]
        simp only [setIntegral_isFundamentalDomain_comp_mul_right μ Γ 𝓕 h𝓕 f hfl]
        simp
    _ = _ := hFeq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.TDat

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem exists_fv (h : A.Ok T) (P : ST) (c : S.Cl) :
    ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  let g : A.N c.1 (S.rep c) →ₗ[𝓞 E] Res P.1 :=
    { toFun := fun x => A.f c.1 (S.rep c) P x
      map_add' := fun x y => h.f_add _ _ _ _ x.2 _ y.2
      map_smul' := fun a x => by
        have := h.f_smul _ _ P a _ x.2
        simp only [RingHom.id_apply]
        rw [Submodule.coe_smul, this]
        rfl }
  have hk : P.1.asIdeal • (⊤ : Submodule (𝓞 E) (A.N c.1 (S.rep c))) ≤ LinearMap.ker g := by
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    show Ideal.Quotient.mk P.1.asIdeal a * g x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let g' : A.lv P c →ₗ[𝓞 E] Res P.1 := Submodule.liftQ _ g hk
  refine ⟨{ toFun := g', map_add' := g'.map_add, map_smul' := ?_ }, fun x => rfl⟩
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact g'.map_smul a x

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hx := A.exists_fv h P c
  unfold fv
  rw [dite_eq_left hx]
  exact hx.choose_spec x

theorem fv_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.fv P c ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne c.1 (S.rep c) P
  intro h0
  have := A.fv_mk h P c ⟨x, hx⟩
  rw [h0] at this
  exact hne this.symm

theorem exists_f_eq_one (h : A.Ok T) (b : S.β) (d : S.D b) (P : ST) : ∃ e ∈ A.N b d, A.f b d P e = 1 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne b d P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (A.f b d P x)⁻¹
  refine ⟨a • x, (A.N b d).smul_mem a hx, ?_⟩
  rw [h.f_smul b d P a x hx, ha]
  exact inv_mul_cancel₀ hne

theorem te_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.te T P c ≠ 0 := by
  have hx : ∃ t : A.dnN c.1 (S.rep c) P, ∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧
      (t : Fin n → E) = (T : 𝓞 E) • e := by
    obtain ⟨e, he, h1⟩ := A.exists_f_eq_one h c.1 (S.rep c) P
    exact ⟨⟨_, (h.te_mem _ _ P e he h1).1⟩, e, he, h1, rfl⟩
  unfold te
  rw [dite_eq_left hx]
  obtain ⟨e, he, h1, ht⟩ := hx.choose_spec
  intro h0
  rw [Submodule.Quotient.mk_eq_zero] at h0
  apply (h.te_mem _ _ P e he h1).2
  rw [← ht]
  have := Submodule.mem_map_of_mem (f := (A.dnN c.1 (S.rep c) P).subtype) h0
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
  exact this

end GlobalTheory.Mem.Col2.TDat

namespace GlobalTheory.Mem.Col2

theorem fv_te_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧
    (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 :=
  fun A _ _ h => ⟨A.fv_mk h, A.fv_ne_zero h, A.te_ne_zero h⟩

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLawsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_levelVector_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧ (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 := by
  first | exact @GlobalTheory.Mem.Col2.fv_te_laws | exact GlobalTheory.Mem.Col2.fv_te_laws | (intros; apply GlobalTheory.Mem.Col2.fv_te_laws <;> assumption)
end
end
