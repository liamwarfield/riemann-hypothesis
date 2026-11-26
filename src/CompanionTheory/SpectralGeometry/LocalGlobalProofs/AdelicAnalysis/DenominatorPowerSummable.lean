module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummable
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.DenSum

variable {F : Type} [Field F] [NumberField F]

noncomputable def dI (b : F) : Ideal (𝓞 F) :=
  Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F b) (1 : Submodule (𝓞 F) F)

theorem den_eq (b : F) : den b = Ideal.absNorm (dI b) := rfl

theorem mem_dI {b : F} {x : 𝓞 F} : x ∈ dI b ↔ ∃ t : 𝓞 F, (t : F) = (x : F) * b := by
  simp only [dI, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one,
    Algebra.smul_def]

theorem dI_add (b : F) (r : 𝓞 F) : dI (b + (r : F)) = dI b := by
  ext x
  rw [mem_dI, mem_dI]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t - x * r, by push_cast; linear_combination ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t + x * r, by push_cast; linear_combination ht⟩

theorem dI_ne_bot (b : F) : dI b ≠ ⊥ := by
  intro h
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) b
  have hmem : (s : 𝓞 F) ∈ dI b := mem_dI.mpr ⟨a, by rw [mul_comm]; exact hs.symm⟩
  rw [h, Ideal.mem_bot] at hmem
  exact nonZeroDivisors.coe_ne_zero s hmem

theorem fibre_bound (N : ℕ) (hN : 0 < N) (s : Set F)
    (hs : ∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b')
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Finite {b : s // dI (b : F) = I} ∧
      Nat.card {b : s // dI (b : F) = I} ≤ N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
  classical
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = Ideal.absNorm I := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by rw [ha_def, Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have haI : (a : 𝓞 F) ∈ I := by rw [ha_def]; exact Ideal.absNorm_mem I
  obtain ⟨C, hC⟩ : I ∣ Ideal.span {(a : 𝓞 F)} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr haI)
  have hspan_ne : Ideal.span {(a : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast ha0
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hC
    exact hspan_ne hC
  have hex : ∀ b : {b : s // dI (b : F) = I}, ∃ t : 𝓞 F, (t : F) = (a : F) * ((b : s) : F) := by
    rintro ⟨b, hb⟩
    have hm : (a : 𝓞 F) ∈ dI (b : F) := by rw [hb]; exact haI
    obtain ⟨t, ht⟩ := mem_dI.mp hm
    exact ⟨t, by rw [ht]; push_cast; rfl⟩
  choose t ht using hex
  have htC : ∀ b, t b ∈ C := by
    intro b
    have hle : Ideal.span {t b} * I ≤ I * C := by
      rw [← hC, Ideal.span_singleton_mul_le_iff]
      intro z hz
      have hz' : z ∈ dI ((b : s) : F) := by rw [b.2]; exact hz
      obtain ⟨u, hu⟩ := mem_dI.mp hz'
      rw [Ideal.mem_span_singleton']
      refine ⟨u, ?_⟩
      apply IsFractionRing.injective (𝓞 F) F
      have hu' : algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F z * ((b : s) : F) := hu
      have ht' : algebraMap (𝓞 F) F (t b) = (a : F) * ((b : s) : F) := ht b
      rw [map_mul, map_mul, map_natCast, hu', ht']
      ring
    have hdvd : I * C ∣ I * Ideal.span {t b} := by
      rw [mul_comm I (Ideal.span _)]
      exact Ideal.dvd_iff_le.mpr hle
    have h2 := (mul_dvd_mul_iff_left hI).mp hdvd
    exact (Ideal.span_singleton_le_iff_mem C).mp (Ideal.dvd_iff_le.mp h2)
  let H : AddSubgroup (𝓞 F) := (Ideal.span {((a * N : ℕ) : 𝓞 F)}).toAddSubgroup
  let K : AddSubgroup (𝓞 F) := C.toAddSubgroup
  have haC : (a : 𝓞 F) ∈ C := by
    have h1 : (a : 𝓞 F) ∈ I * C := by rw [← hC]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : C * I ≤ C) (by rwa [mul_comm] at h1)
  have hHK : H ≤ K := by
    intro x hx
    have hle : Ideal.span {((a * N : ℕ) : 𝓞 F)} ≤ C := by
      rw [Ideal.span_singleton_le_iff_mem]
      push_cast
      exact C.mul_mem_right _ haC
    exact hle hx
  let Φ : {b : s // dI (b : F) = I} → K ⧸ H.addSubgroupOf K := fun b => QuotientAddGroup.mk ⟨t b, htC b⟩
  have hΦ : Function.Injective Φ := by
    intro b b' hbb
    have hmem := QuotientAddGroup.eq.mp hbb
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hr' : r * ((a * N : ℕ) : 𝓞 F) = -t b + t b' := by simpa using hr
    have h1 := congrArg (algebraMap (𝓞 F) F) hr'
    have htb : algebraMap (𝓞 F) F (t b) = (a : F) * ((b.1 : s) : F) := ht b
    have htb' : algebraMap (𝓞 F) F (t b') = (a : F) * ((b'.1 : s) : F) := ht b'
    simp only [map_mul, map_add (f := _), map_neg, map_natCast, Nat.cast_mul, htb, htb'] at h1
    have hrF : algebraMap (𝓞 F) F r = (r : F) := rfl
    rw [hrF] at h1
    have ha' : (a : F) ≠ 0 := by exact_mod_cast ha0
    have key : ((b'.1 : s) : F) - ((b.1 : s) : F) = (N : F) * (r : F) := by
      apply mul_left_cancel₀ ha'
      linear_combination -h1
    have := hs _ b'.1.2 _ b.1.2 ⟨r, key⟩
    exact Subtype.ext (Subtype.ext this.symm)
  have hnormNat : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F) := by
    intro m
    rw [Ideal.absNorm_span_singleton]
    have hm : (m : 𝓞 F) = algebraMap ℤ (𝓞 F) (m : ℤ) := by simp
    rw [hm, Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  have hrel : H.relIndex K = N ^ Module.finrank ℤ (𝓞 F) * a := by
    have h1 := AddSubgroup.relIndex_mul_index hHK
    have hKi : K.index = Ideal.absNorm C := by rw [Ideal.absNorm_apply]; rfl
    have hHi : H.index = (a * N) ^ Module.finrank ℤ (𝓞 F) := by
      have h3 : H.index = Ideal.absNorm (Ideal.span {((a * N : ℕ) : 𝓞 F)}) := by rw [Ideal.absNorm_apply]; rfl
      rw [h3, hnormNat]
    have hmul : Ideal.absNorm (Ideal.span {(a : 𝓞 F)}) = a * Ideal.absNorm C := by rw [hC, map_mul, ha_def]
    have hC0' : Ideal.absNorm C ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [hKi, hHi] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hC0')
    rw [h1, mul_pow, ← hnormNat a, hmul]
    ring
  haveI hfinQ : Finite (K ⧸ H.addSubgroupOf K) := Nat.finite_of_card_ne_zero (by
    show H.relIndex K ≠ 0
    rw [hrel]
    exact Nat.mul_ne_zero (pow_ne_zero _ hN.ne') ha0)
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card {b : s // dI (b : F) = I} ≤ Nat.card (K ⧸ H.addSubgroupOf K) := Nat.card_le_card_of_injective Φ hΦ
    _ = N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
      show H.relIndex K = _
      rw [hrel, ha_def]

theorem summable_den :
    ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  intro F _ _ M hM N hN
  refine ⟨fun b r => by rw [den_eq, den_eq, dI_add], fun b => ?_, fun s hs => ?_⟩
  · rw [den_eq]
    exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact dI_ne_bot b)
  · have hsum2 := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).1
    have hfin : ∀ I : Ideal (𝓞 F), Finite {b : s // dI (b : F) = I} := by
      intro I
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        infer_instance
      · exact (fibre_bound N hN s hs I hI).1
    let f : s → ℝ := fun b => ((den (b : F) : ℝ) ^ M)⁻¹
    show Summable f
    rw [← (Equiv.sigmaFiberEquiv (fun b : s => dI (b : F))).summable_iff]
    refine (summable_sigma_of_nonneg (fun _ => by simp only [Function.comp, f]; positivity)).mpr ⟨fun I => ?_, ?_⟩
    · haveI := hfin I
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le (fun I => tsum_nonneg (fun _ => by simp only [Function.comp, f]; positivity)) (fun I => ?_)
        (hsum2.mul_left ((N : ℝ) ^ Module.finrank ℤ (𝓞 F)))
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        rw [tsum_empty]
        positivity
      · have hterm : ∀ y : {b : s // dI (b : F) = I},
            (f ∘ ⇑(Equiv.sigmaFiberEquiv fun b : s => dI (b : F))) ⟨I, y⟩ = ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
          rintro ⟨b, hb⟩
          simp [f, den_eq, hb]
        rw [tsum_congr hterm, tsum_const, nsmul_eq_mul]
        have hc := (fibre_bound N hN s hs I hI).2
        have hn1 : (1 : ℝ) ≤ Ideal.absNorm I := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
        calc (Nat.card {b : s // dI (b : F) = I} : ℝ) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹
            ≤ ((N : ℝ) ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
              gcongr
              exact_mod_cast hc
          _ ≤ (N : ℝ) ^ Module.finrank ℤ (𝓞 F) * (Ideal.absNorm I : ℝ) ^ (-(2:ℝ)) := by
              rw [Real.rpow_neg (by positivity), mul_assoc]
              gcongr
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              have ha : (0:ℝ) < Ideal.absNorm I := by linarith
              have hM1 : (Ideal.absNorm I : ℝ) ^ M = (Ideal.absNorm I : ℝ) * (Ideal.absNorm I : ℝ) ^ (M - 1) := by
                rw [← pow_succ']
                congr 1
                omega
              rw [hM1, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
              exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn1 (by omega))

end GlobalTheory.CompanionTheory.SW.DenSum
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummableStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_power_summable : ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.DenSum.summable_den | exact GlobalTheory.CompanionTheory.SW.DenSum.summable_den | (intros; apply GlobalTheory.CompanionTheory.SW.DenSum.summable_den <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PoissonSummationGaussian
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PoissonSummationGaussian
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PoiLat

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem quad_mulVec (P : Matrix κ κ ℝ) (W : Matrix κ κ ℂ) (v : κ → ℝ) :
    (fun i => (((P *ᵥ v) i : ℝ) : ℂ)) ⬝ᵥ (W *ᵥ fun i => (((P *ᵥ v) i : ℝ) : ℂ)) =
      (fun i => (v i : ℂ)) ⬝ᵥ
        (((P.map Complex.ofReal)ᵀ * W * P.map Complex.ofReal) *ᵥ fun i => (v i : ℂ)) := by
  rw [GlobalTheory.ofReal_mulVec_eq, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => (v i : ℂ)) ((P.map Complex.ofReal)ᵀ), Matrix.vecMul_transpose]

theorem contragredient_congr {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) (Z : Matrix κ κ ℂ) :
    (((g⁻¹)ᵀ).map Complex.ofReal)ᵀ * Z⁻¹ * ((g⁻¹)ᵀ).map Complex.ofReal =
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹ := by
  have hC : (g⁻¹).map Complex.ofReal = (g.map Complex.ofReal)⁻¹ := (GlobalTheory.inv_map_ofReal hg).symm
  have hC' : ((g⁻¹)ᵀ).map Complex.ofReal = ((g.map Complex.ofReal)⁻¹)ᵀ := by
    rw [Matrix.transpose_map, hC]
  rw [hC', Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem gaussian_lattice_term (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0)
    (a : κ → ℝ) (n : κ → ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z *ᵥ fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
        ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n := by
  have hv : a + g *ᵥ (fun i => (n i : ℝ)) = g *ᵥ ((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg),
      Matrix.one_mulVec, add_comm]
  have hs : (fun i => ((((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) i : ℝ) : ℂ)) =
      ReciprocityTheory.PTheta.shiftVec (g⁻¹ *ᵥ a) n := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  rw [hv, quad_mulVec, hs]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero]
  congr 1
  ring

theorem gaussian_fourier {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) (y : κ → ℝ) :
    ∫ x : κ → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)) =
      GlobalTheory.siegelGaussIntegral Z * Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => (y i : ℂ)) ⬝ᵥ (Z⁻¹ *ᵥ fun i => (y i : ℂ)))) := by
  have hq := hZ.integral_cexp_quadratic (fun i => (y i : ℂ))
  rw [← hq]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  have hxy : ((x ⬝ᵥ y : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (y i : ℂ)) := by
    simp [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hxy]
  ring

theorem siegelGaussIntegral_congr (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) :
    GlobalTheory.siegelGaussIntegral ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) =
      ((|g.det|⁻¹ : ℝ) : ℂ) * GlobalTheory.siegelGaussIntegral Z := by
  have hv : Continuous fun y : κ → ℝ => fun i => (y i : ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hf : Continuous fun y : κ → ℝ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (y i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (y i : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul (hv.dotProduct (continuous_const.matrix_mulVec hv)))
  have key := GlobalTheory.integral_comp_mulVec_of_det_ne_zero hg hf
  simp only [quad_mulVec] at key
  simp only [GlobalTheory.siegelGaussIntegral]
  rw [← abs_inv]
  exact key

theorem fourier_lattice_term {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) {g : Matrix κ κ ℝ}
    (hg : g.det ≠ 0) (n : κ → ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z⁻¹ *ᵥ fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  have hs : ReciprocityTheory.PTheta.shiftVec (0 : κ → ℝ) n = fun i => (((n i : ℝ)) : ℂ) := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  rw [quad_mulVec, contragredient_congr hg]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero, hs, Matrix.neg_mulVec, dotProduct_neg]
  congr 1
  ring

theorem phase_lattice {g : Matrix κ κ ℝ} (a : κ → ℝ) (n : κ → ℤ) :
    ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ) =
      (fun i => (n i : ℂ)) ⬝ᵥ fun i => ((g⁻¹ *ᵥ a) i : ℂ) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem poisson_shifted_lattice : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ),
    Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ,
    let f : (κ → ℝ) → ℂ | x => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ))));
    let fh : (κ → ℝ) → ℂ | y => (∫ x,
      f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)));
    Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧
      Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧
      (∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ))) = ((|g.det|⁻¹ : ℝ) : ℂ) *
        ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  intro κ _ _ Z hs hp g hg a f fh
  have hZ : GlobalTheory.IsSiegel Z := ⟨hs, hp⟩
  have hσ := hZ.transpose_mul_mul hg
  have hf : ∀ n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n :=
    fun n => gaussian_lattice_term Z hg a n
  have hfh : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) = GlobalTheory.siegelGaussIntegral Z *
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
    intro n
    rw [← fourier_lattice_term hZ hg n]
    exact gaussian_fourier hZ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hf]
    exact hσ.summable_norm_riemannThetaTerm _ _ _
  · simp only [hfh, norm_mul]
    exact (hσ.neg_inv.summable_norm_riemannThetaTerm _ _ _).mul_left _
  · have hterm : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) = GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 (-(g⁻¹ *ᵥ a))
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
      intro n
      rw [hfh, phase_lattice, mul_assoc]
      congr 1
      rw [GlobalTheory.riemannThetaTerm_zero_zero, GlobalTheory.riemannThetaTerm_def, ← Complex.exp_add]
      congr 1
      simp [dotProduct]
      ring
    simp only [hf, hterm]
    rw [tsum_mul_left, ← mul_assoc, ← siegelGaussIntegral_congr Z hg]
    have h0 := hσ.riemannTheta_eq_neg_inv (g⁻¹ *ᵥ a) 0
    have h1 := GlobalTheory.riemannTheta_neg 0 (g⁻¹ *ᵥ a)
      (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0
    simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h0 h1
    rw [h1] at h0
    exact h0

end GlobalTheory.CompanionTheory.SW.Core.PoiLat
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PoissonSummationGaussianStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory.CompanionTheory.SW.Core.PoiLat in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_gaussian :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ),
    Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ,
    let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ))));
    let fh : (κ → ℝ) → ℂ := fun y =>
      ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ));
    Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧
      Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧
      (∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ))) = ((|g.det|⁻¹ : ℝ) : ℂ) *
        ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  intro κ _ _ Z hs hp g hg a f fh
  have hZ : GlobalTheory.IsSiegel Z := ⟨hs, hp⟩
  have hσ := hZ.transpose_mul_mul hg
  have hf : ∀ n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) =
      GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
        ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n :=
    fun n => gaussian_lattice_term Z hg a n
  have hfh : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) =
      GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 0
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
    intro n
    rw [← fourier_lattice_term hZ hg n]
    exact gaussian_fourier hZ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hf]
    exact hσ.summable_norm_riemannThetaTerm _ _ _
  · simp only [hfh, norm_mul]
    exact (hσ.neg_inv.summable_norm_riemannThetaTerm _ _ _).mul_left _
  · have hterm : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) =
      GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 (-(g⁻¹ *ᵥ a))
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
      intro n
      rw [hfh, phase_lattice, mul_assoc]
      congr 1
      rw [GlobalTheory.riemannThetaTerm_zero_zero, GlobalTheory.riemannThetaTerm_def,
        ← Complex.exp_add]
      congr 1
      simp [dotProduct]
      ring
    simp only [hf, hterm]
    rw [tsum_mul_left, ← mul_assoc, ← siegelGaussIntegral_congr Z hg]
    have h0 := hσ.riemannTheta_eq_neg_inv (g⁻¹ *ᵥ a) 0
    have h1 := GlobalTheory.riemannTheta_neg 0 (g⁻¹ *ᵥ a)
      (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0
    simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h0 h1
    rw [h1] at h0
    exact h0
end
end
