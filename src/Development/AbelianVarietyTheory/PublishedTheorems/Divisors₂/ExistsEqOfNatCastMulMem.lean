module

public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoCoeffZero
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology

namespace GlobalTheory.DiscUniformisation

lemma tendsto_coeff_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto f atImInfty (𝓝 ((qExpansion 1 f).coeff 0)) := by
  have hp := one_mem_strictPeriods_SL
  have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hp
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hp
  rw [UpperHalfPlane.qExpansion_coeff_zero one_pos han hper,
    ← UpperHalfPlane.cuspFunction_apply_zero one_pos han hper]
  refine (han.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)).congr
    fun τ => ?_
  exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper

lemma tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : Tendsto (E hk) atImInfty (𝓝 1) := by
  have h := tendsto_coeff_zero (E hk)
  rwa [EisensteinSeries.E_qExpansion_coeff_zero hk hk2] at h

lemma exists_zero (F : ModularForm 𝒮ℒ 12) (c : ℂ) (hc : c ≠ 0)
    (hF : Tendsto F atImInfty (𝓝 c)) : ∃ z, F z = 0 := by
  by_contra hne
  push_neg at hne

  have hD0 : Tendsto ModularForm.discriminant atImInfty (𝓝 0) := by
    have h1 := tendsto_coeff_zero (ModularFormClass.modularForm CuspForm.discriminant)
    rw [ModularFormClass.coe_modularForm,
      CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL,
      CuspForm.coe_discriminant] at h1
    exact h1
  have hG0 : Tendsto (fun τ => ModularForm.discriminant τ / F τ) atImInfty (𝓝 0) := by
    have h := hD0.div hF hc
    rw [zero_div] at h
    exact h

  let G0 : SlashInvariantForm 𝒮ℒ 0 :=
    { toFun := fun τ => ModularForm.discriminant τ / F τ
      slash_action_eq' := by
        rintro γ ⟨g, rfl⟩
        funext τ
        have key : SlashAction.map (0 : ℤ) g (fun τ => ModularForm.discriminant τ / F τ) τ =
            ModularForm.discriminant τ / F τ := by
          rw [ModularForm.slash_action_eq'_iff, zpow_zero, one_mul]
          have hΔ := (ModularForm.slash_action_eq'_iff 12 (⇑CuspForm.discriminant) g τ).1
            (congrFun (SlashInvariantForm.slash_action_eqn CuspForm.discriminant _ ⟨g, rfl⟩) τ)
          have hF' := (ModularForm.slash_action_eq'_iff 12 (⇑F) g τ).1
            (congrFun (SlashInvariantForm.slash_action_eqn F _ ⟨g, rfl⟩) τ)
          rw [CuspForm.coe_discriminant] at hΔ
          show ModularForm.discriminant (g • τ) / F (g • τ) = ModularForm.discriminant τ / F τ
          have hd : ∀ x : ℂ, ModularForm.discriminant (g • τ) = x * ModularForm.discriminant τ → x ≠ 0 := by
            rintro x hx rfl
            rw [zero_mul] at hx
            exact ModularForm.discriminant_ne_zero _ hx
          have hx0 := hd _ hΔ
          rw [hΔ, hF']
          rw [mul_div_mul_left _ _ hx0]
        exact key }
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty G0.toFun :=
    UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty hG0
  let G : ModularForm 𝒮ℒ 0 :=
    { toSlashInvariantForm := G0
      holo' := (ModularFormClass.holo CuspForm.discriminant).div (ModularFormClass.holo F) hne
      bdd_at_cusps' := by
        intro c' hc'
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
        intro γ _
        convert hbdd using 1
        exact G0.slash_action_eq' _ ⟨γ, rfl⟩ }
  obtain ⟨c', hc'⟩ := ModularForm.eq_const_of_weight_zero G
  have hGt : Tendsto (⇑G) atImInfty (𝓝 0) := hG0
  rw [hc'] at hGt
  have hc0 : c' = 0 := tendsto_nhds_unique tendsto_const_nhds hGt
  have h1 : G UpperHalfPlane.I = 0 := by rw [hc', Function.const_apply, hc0]
  have h2 : ModularForm.discriminant UpperHalfPlane.I / F UpperHalfPlane.I = 0 := h1
  rcases div_eq_zero_iff.1 h2 with h3 | h3
  · exact ModularForm.discriminant_ne_zero _ h3
  · exact hne _ h3

lemma E_cube_ne (z : ℍ) : E₄ z ^ 3 ≠ E₆ z ^ 2 := by
  intro h
  apply ModularForm.discriminant_ne_zero z
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, sub_self, zero_div]

lemma exists_ratio (A B : ℂ) (h : A ^ 3 ≠ B ^ 2) :
    ∃ z : ℍ, B ^ 2 * E₄ z ^ 3 = A ^ 3 * E₆ z ^ 2 := by
  let F4 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (E₄.mul (E₄.mul E₄))
  let F6 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (E₆.mul E₆)
  let F : ModularForm 𝒮ℒ 12 := B ^ 2 • F4 - A ^ 3 • F6
  have hF : ∀ z, F z = B ^ 2 * E₄ z ^ 3 - A ^ 3 * E₆ z ^ 2 := by
    intro z
    show B ^ 2 * (E₄ z * (E₄ z * E₄ z)) - A ^ 3 * (E₆ z * E₆ z) = _
    ring
  have t4 : Tendsto (⇑E₄) atImInfty (𝓝 1) := tendsto_E (k := 4) (by norm_num) (by decide)
  have t6 : Tendsto (⇑E₆) atImInfty (𝓝 1) := tendsto_E (k := 6) (by norm_num) (by decide)
  have tF : Tendsto F atImInfty (𝓝 (B ^ 2 - A ^ 3)) := by
    have h1 : Tendsto (fun z => B ^ 2 * E₄ z ^ 3 - A ^ 3 * E₆ z ^ 2) atImInfty
        (𝓝 (B ^ 2 * 1 ^ 3 - A ^ 3 * 1 ^ 2)) :=
      ((t4.pow 3).const_mul _).sub ((t6.pow 2).const_mul _)
    simp only [one_pow, mul_one] at h1
    exact h1.congr fun z => (hF z).symm
  have hc : B ^ 2 - A ^ 3 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  obtain ⟨z, hz⟩ := exists_zero F _ hc tF
  refine ⟨z, ?_⟩
  rw [hF] at hz
  exact sub_eq_zero.1 hz

lemma exists_scale (A B a b : ℂ) (h : A ^ 3 ≠ B ^ 2) (h' : a ^ 3 ≠ b ^ 2)
    (e : B ^ 2 * a ^ 3 = A ^ 3 * b ^ 2) : ∃ μ : ℂ, μ ≠ 0 ∧ μ ^ 4 * a = A ∧ μ ^ 6 * b = B := by
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      exact h' (by ring)
    have hA : A = 0 := by
      have h0 : A ^ 3 * b ^ 2 = 0 := by rw [← e]; ring
      exact pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 2 hb))
    subst hA
    have hB : B ≠ 0 := by
      rintro rfl
      exact h (by ring)
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (B / b) (by norm_num : 0 < 6)
    refine ⟨μ, ?_, by ring, ?_⟩
    · rintro rfl
      rw [zero_pow (by norm_num)] at hμ
      exact hB ((div_eq_zero_iff.1 hμ.symm).resolve_right hb)
    · rw [hμ, div_mul_cancel₀ B hb]
  · by_cases hb : b = 0
    · subst hb
      have hB : B = 0 := by
        have h0 : B ^ 2 * a ^ 3 = 0 := by rw [e]; ring
        exact pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 3 ha))
      subst hB
      have hA : A ≠ 0 := by
        rintro rfl
        exact h (by ring)
      obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (A / a) (by norm_num : 0 < 4)
      refine ⟨μ, ?_, ?_, by ring⟩
      · rintro rfl
        rw [zero_pow (by norm_num)] at hμ
        exact hA ((div_eq_zero_iff.1 hμ.symm).resolve_right ha)
      · rw [hμ, div_mul_cancel₀ A ha]
    · have hA : A ≠ 0 := by
        rintro rfl
        have h0 : B ^ 2 * a ^ 3 = 0 := by rw [e]; ring
        have hB : B = 0 :=
          pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 3 ha))
        exact h (by rw [hB]; ring)
      have hB : B ≠ 0 := by
        rintro rfl
        have h0 : A ^ 3 * b ^ 2 = 0 := by rw [← e]; ring
        exact hA (pow_eq_zero_iff (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right (pow_ne_zero 2 hb)))
      have hAb : A * b ≠ 0 := mul_ne_zero hA hb
      obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (B * a / (A * b)) (by norm_num : 0 < 2)
      refine ⟨μ, ?_, ?_, ?_⟩
      · rintro rfl
        rw [zero_pow (by norm_num)] at hμ
        exact div_ne_zero (mul_ne_zero hB ha) hAb hμ.symm
      · have h4 : μ ^ 4 = (B * a / (A * b)) ^ 2 := by rw [← hμ]; ring
        rw [h4, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hAb)]
        linear_combination e
      · have h6 : μ ^ 6 = (B * a / (A * b)) ^ 3 := by rw [← hμ]; ring
        rw [h6, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hAb)]
        linear_combination B * b * e

lemma G_eq (L : PeriodPair) (z : ℍ) (hz : L.ω₁ = L.ω₂ * z) {k : ℕ} (hk : 3 ≤ k) :
    L.G k = (L.ω₂⁻¹) ^ k * (2 * riemannZeta k * E hk z) := by
  have hE : E hk z = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 (k : ℤ) z := rfl
  calc L.G k = ∑' v : Fin 2 → ℤ, (L.ω₂⁻¹) ^ k * EisensteinSeries.eisSummand k v z := by
        unfold PeriodPair.G
        rw [← (L.latticeEquivProd.symm.toEquiv).tsum_eq, ← (finTwoArrowEquiv ℤ).tsum_eq]
        congr 1
        funext v
        simp only [EisensteinSeries.eisSummand, zpow_natCast]
        have e : (v 0 : ℂ) * L.ω₁ + v 1 * L.ω₂ = L.ω₂ * (v 0 * z + v 1) := by rw [hz]; ring
        have hcoord : (L.latticeEquivProd.symm.toEquiv ((finTwoArrowEquiv ℤ) v) : ℂ) =
            (v 0 : ℂ) * L.ω₁ + v 1 * L.ω₂ := by
          simp [PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply,
            Finsupp.sum_fintype, PeriodPair.latticeBasis]
        rw [hcoord]
        rw [e, mul_pow, mul_inv, inv_pow]
        congr 1
        try simp [one_div]
    _ = (L.ω₂⁻¹) ^ k * (riemannZeta k * eisensteinSeries (N := 1) 0 (k : ℤ) z) := by
        rw [tsum_mul_left, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z]
    _ = _ := by rw [hE]; ring

lemma zeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h6 : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
      bernoulli'_four, h5, Nat.choose]
    norm_num
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 : ℂ) * ((3 : ℕ) : ℂ) = 6 by norm_num, h6] at h
  rw [h]
  norm_num [Nat.factorial]
  ring

lemma g_eq (L : PeriodPair) (z : ℍ) (hz : L.ω₁ = L.ω₂ * z) :
    L.g₂ = 4 / 3 * ((Real.pi * L.ω₂⁻¹) ^ 4 * E₄ z) ∧
      L.g₃ = 8 / 27 * ((Real.pi * L.ω₂⁻¹) ^ 6 * E₆ z) := by
  have h4 := G_eq L z hz (by norm_num : 3 ≤ 4)
  have h6 := G_eq L z hz (by norm_num : 3 ≤ 6)
  have e4 : (E (by norm_num : 3 ≤ 4)) z = E₄ z := rfl
  have e6 : (E (by norm_num : 3 ≤ 6)) z = E₆ z := rfl
  rw [e4] at h4
  rw [e6] at h6
  simp only [Nat.cast_ofNat] at h4 h6
  rw [riemannZeta_four] at h4
  rw [zeta_six] at h6
  unfold PeriodPair.g₂ PeriodPair.g₃
  rw [h4, h6]
  constructor <;> ring

lemma ω₂_ne_zero (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

lemma im_ne_zero (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have hω := ω₂_ne_zero L
  set r := (L.ω₁ / L.ω₂).re with hr
  have hz : L.ω₁ / L.ω₂ = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [h])
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hz]; field_simp
  have h2 := (LinearIndependent.pair_iff.1 L.indep) 1 (-r) (by
    rw [one_smul, Complex.real_smul, h1]
    push_cast
    ring)
  exact one_ne_zero h2.1

def swap (L : PeriodPair) : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := L.ω₁
  indep := LinearIndependent.pair_symm_iff.mp L.indep

lemma swap_G (L : PeriodPair) (k : ℕ) : (swap L).G k = L.G k := by
  unfold PeriodPair.G PeriodPair.lattice
  show ∑' (l : ↥(Submodule.span ℤ {L.ω₂, L.ω₁})), ((l : ℂ) ^ k)⁻¹ = _
  rw [Set.pair_comm L.ω₂ L.ω₁]

lemma disc_of_pos (L : PeriodPair) (h : 0 < (L.ω₁ / L.ω₂).im) : L.g₂ ^ 3 ≠ 27 * L.g₃ ^ 2 := by
  intro hc
  have hω := ω₂_ne_zero L
  set z : ℍ := UpperHalfPlane.mk (L.ω₁ / L.ω₂) h with hzdef
  have hz : L.ω₁ = L.ω₂ * z := by
    rw [hzdef, UpperHalfPlane.coe_mk]
    field_simp
  obtain ⟨e2, e3⟩ := g_eq L z hz
  rw [e2, e3] at hc
  apply E_cube_ne z
  have hπ : ((Real.pi : ℂ) * L.ω₂⁻¹) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (inv_ne_zero hω)
  have h0 : ((Real.pi : ℂ) * L.ω₂⁻¹) ^ 12 * (64 / 27) * (E₄ z ^ 3 - E₆ z ^ 2) = 0 := by
    linear_combination hc
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exfalso
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact pow_ne_zero _ hπ h2
    · norm_num at h2
  · exact sub_eq_zero.1 h1

lemma disc (L : PeriodPair) : L.g₂ ^ 3 ≠ 27 * L.g₃ ^ 2 := by
  rcases lt_or_gt_of_ne (im_ne_zero L) with h | h
  · have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
    have h' : 0 < ((swap L).ω₁ / (swap L).ω₂).im := by
      show 0 < (L.ω₂ / L.ω₁).im
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.2 h) (Complex.normSq_pos.2 (div_ne_zero hω₁ (ω₂_ne_zero L)))
    have h2 := disc_of_pos (swap L) h'
    have e2 : (swap L).g₂ = L.g₂ := by simp only [PeriodPair.g₂, swap_G]
    have e3 : (swap L).g₃ = L.g₃ := by simp only [PeriodPair.g₃, swap_G]
    rwa [e2, e3] at h2
  · exact disc_of_pos L h

lemma uniformisation (a b : ℂ) (h : a ^ 3 ≠ 27 * b ^ 2) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  have hAB : (3 / 4 * a) ^ 3 ≠ (27 / 8 * b) ^ 2 := by
    intro hc
    apply h
    linear_combination (64 / 27) * hc
  obtain ⟨z, hz⟩ := exists_ratio (3 / 4 * a) (27 / 8 * b) hAB
  obtain ⟨μ, hμ0, hμ4, hμ6⟩ := exists_scale (3 / 4 * a) (27 / 8 * b) (E₄ z) (E₆ z) hAB (E_cube_ne z) hz
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω : (Real.pi : ℂ) / μ ≠ 0 := div_ne_zero hπ hμ0
  have hzim : 0 < (z : ℂ).im := by simpa using z.im_pos
  have hind : LinearIndependent ℝ ![(Real.pi : ℂ) / μ * z, (Real.pi : ℂ) / μ] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    rw [Complex.real_smul, Complex.real_smul] at hst
    have h1 : ((s : ℂ) * z + t) * ((Real.pi : ℂ) / μ) = 0 := by linear_combination hst
    have h2 : (s : ℂ) * z + t = 0 := (mul_eq_zero.1 h1).resolve_right hω
    have h3 : s * (z : ℂ).im = 0 := by
      have := congrArg Complex.im h2
      simpa using this
    have hs : s = 0 := (mul_eq_zero.1 h3).resolve_right hzim.ne'
    refine ⟨hs, ?_⟩
    rw [hs] at h2
    simpa using h2
  let L : PeriodPair := ⟨(Real.pi : ℂ) / μ * z, (Real.pi : ℂ) / μ, hind⟩
  obtain ⟨e2, e3⟩ := g_eq L z rfl
  have hπω : (Real.pi : ℂ) * L.ω₂⁻¹ = μ := by
    show (Real.pi : ℂ) * ((Real.pi : ℂ) / μ)⁻¹ = μ
    field_simp
  refine ⟨L, ?_, ?_⟩
  · rw [e2, hπω, hμ4]
    ring
  · rw [e3, hπω, hμ6]
    ring

theorem main (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  apply uniformisation
  intro h
  apply disc L
  apply σ.injective
  simp only [map_pow, map_mul, map_ofNat]
  exact h

end GlobalTheory.DiscUniformisation
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open WeierstrassCurve

theorem exists_conj_lattice (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  first
  | exact @_root_.GlobalTheory.DiscUniformisation.main
  | exact _root_.GlobalTheory.DiscUniformisation.main
  | (apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiscUniformisation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiscUniformisation.main ..)

end GlobalTheory.CMRam
end
end

open NumberField Neutral.B1 GlobalTheory.Idele GlobalTheory.ConjPoint Filter
open scoped nonZeroDivisors IntermediateField Topology

noncomputable section

namespace GlobalTheory.EllipticCM

def IsAnalyticIso {X : WeierstrassCurve ℂ} {Λ : AddSubgroup ℂ}
    (ξ : (ℂ ⧸ Λ) ≃+ X.toAffine.Point) : Prop :=
  ∀ z ∉ Λ, ∃ f g : ℂ → ℂ, AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z ∧
    ∀ᶠ w in 𝓝 z, ∃ h, ξ (w : ℂ) = .some (f w) (g w) h

section Defs

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

def idealSub (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : AddSubgroup ℂ :=
  (𝔞 : Submodule (𝓞 K) K).toAddSubgroup.map (algebraMap K ℂ).toAddMonoidHom

def torsionIncl (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :
    (K ⧸ (𝔞 : Submodule (𝓞 K) K)) →+ (ℂ ⧸ idealSub 𝔞) :=
  QuotientAddGroup.map _ _ (algebraMap K ℂ).toAddMonoidHom fun x hx => ⟨x, hx, rfl⟩

def Transports (σ : ℂ ≃ₐ[K] ℂ) (t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ)
    {X : WeierstrassCurve ℂ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0)
    (ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point) : Prop :=
  ∃! ξ' : (ℂ ⧸ idealSub (t⁻¹ • 𝔞)) ≃+ (X.map (σ : ℂ →+* ℂ)).toAffine.Point,
    IsAnalyticIso ξ' ∧ ∀ x : K ⧸ (𝔞 : Submodule (𝓞 K) K),
      mapPoint X (σ : ℂ →+* ℂ) (ξ (torsionIncl 𝔞 x)) =
        ξ' (torsionIncl (t⁻¹ • 𝔞) (mulEquiv t⁻¹ h𝔞 rfl x))

def RestrictsTo (σ : ℂ ≃ₐ[K] ℂ) (a : Field.absoluteGaloisGroupAbelianization K) : Prop :=
  ∃ (ι : AlgebraicClosure K →ₐ[K] ℂ) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
    (∀ x, σ (ι x) = ι (g x)) ∧ toAb K g = a

def finitePart (s : Ideles K) : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) s

end Defs

end GlobalTheory.EllipticCM

namespace GlobalTheory.Published

open GlobalTheory.EllipticCM

def EllipticMainTheoremCM : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K,
      IsGlobalArtinMap K Art →
    ∀ (σ : ℂ ≃ₐ[K] ℂ) (s : Ideles K), RestrictsTo σ (Art (QuotientGroup.mk s)) →
    ∀ (X : WeierstrassCurve ℂ) [X.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
      (ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point), IsAnalyticIso ξ →
      Transports σ (finitePart s) h𝔞 ξ

def HilbertClassFieldJ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ L₀ : PeriodPair, IsIdealLattice (K := K) 1 L₀ →
      IsHilbertClassField K⟮(latticeCurve L₀).j⟯ ∧
      Module.finrank K K⟮(latticeCurve L₀).j⟯ = classNumber K ∧
      (∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
        IsIdealLattice 𝔞 L → IsIdealLattice 𝔟 L' →
        ((latticeCurve L).j = (latticeCurve L').j ↔ ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟)) ∧
      (idealInvariants K).ncard = classNumber K ∧
      Set.range (fun g : K⟮(latticeCurve L₀).j⟯ ≃ₐ[K] K⟮(latticeCurve L₀).j⟯ =>
        (g (IntermediateField.AdjoinSimple.gen K (latticeCurve L₀).j) : ℂ)) = idealInvariants K

theorem ComplexMultiplicationJSt.hilbertClassFieldJ (h : ComplexMultiplicationJSt) :
    HilbertClassFieldJ := by
  intro K _ _ _ _ h2 L₀ hL₀
  obtain ⟨H, art, hH, hart, hgen, hj⟩ := id h K h2
  have hm : ∀ {𝔞 L}, IsIdealLattice (K := K) 𝔞 L → (latticeCurve L).j ∈ H := fun {𝔞 L} hL =>
    hgen 𝔞 L hL ▸ IntermediateField.mem_adjoin_simple_self K _
  have hiff : ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
      IsIdealLattice 𝔞 L → IsIdealLattice 𝔟 L' →
      ((latticeCurve L).j = (latticeCurve L').j ↔ ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟) := by
    intro 𝔞 𝔟 L L' hL hL'
    have hL'' : IsIdealLattice ((𝔞 * 𝔟⁻¹)⁻¹ * 𝔞) L' := by
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right]
    have e := hj 𝔞 _ L L' hL hL'' ⟨_, hm hL⟩ rfl
    rw [← mul_inv_eq_one (a := ClassGroup.mk K 𝔞), ← map_inv, ← map_mul]
    constructor
    · intro hjj
      rw [← hjj] at e
      rw [← map_eq_one_iff art art.injective]
      generalize art (ClassGroup.mk K (𝔞 * 𝔟⁻¹)) = g at e
      have hH' := hgen 𝔞 L hL
      subst hH'
      apply AlgEquiv.coe_toAlgHom_injective
      refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
      rintro x rfl
      exact Subtype.ext e
    · intro hc
      rw [hc, map_one] at e
      exact e
  obtain rfl := hgen 1 L₀ hL₀
  have hrange : Set.range (fun g : K⟮(latticeCurve L₀).j⟯ ≃ₐ[K] K⟮(latticeCurve L₀).j⟯ =>
      (g (IntermediateField.AdjoinSimple.gen K (latticeCurve L₀).j) : ℂ)) = idealInvariants K := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨c, rfl⟩ := art.surjective g
      obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
      obtain ⟨L', hL'⟩ := exists_isIdealLattice h2 ((FractionalIdeal.mk0 K I)⁻¹ * 1)
      refine ⟨_, L', hL', ?_⟩
      rw [← hj 1 _ L₀ L' hL₀ hL' (IntermediateField.AdjoinSimple.gen K _) rfl, ClassGroup.mk_mk0]
    · rintro ⟨𝔠, L', hL', rfl⟩
      exact ⟨art (ClassGroup.mk K 𝔠⁻¹), hj 1 𝔠⁻¹ L₀ L' hL₀ (by simpa using hL') _ rfl⟩
  refine ⟨hH, h.finrank_eq h2 hH, hiff, ?_, hrange⟩
  rw [← hrange, ← Set.image_univ, Set.ncard_image_of_injective, Set.ncard_univ,
    ← Nat.card_congr art.toEquiv, classNumber, Nat.card_eq_fintype_card]
  intro g g' e
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
  rintro x rfl
  exact Subtype.ext e

end GlobalTheory.Published

namespace GlobalTheory.EllipticCM

open WeierstrassCurve

section Analytic

variable {X : WeierstrassCurve ℂ} {Λ : AddSubgroup ℂ} {L : PeriodPair} {C : VariableChange ℂ}

theorem IsAnalyticIso.exists_mul {ξ : (ℂ ⧸ Λ) ≃+ X.toAffine.Point} (hξ : IsAnalyticIso ξ)
    (h : C • X = latticeCurve L) :
    ∃ α : ℂ, α ≠ 0 ∧ (∀ z, z ∈ Λ ↔ α * z ∈ L.lattice) ∧
      ∀ z : ℂ, ξ z = variableChangePoint C h (latticePoint L (α * z)) := by
  have hinj := (variableChangePoint_bijective C h).1
  obtain ⟨q, hq⟩ := ξ.surjective (variableChangePoint C h (latticePoint L (L.ω₁ / 2)))
  obtain ⟨z₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hz₀ : z₀ ∉ Λ := fun hz => by
    rw [(QuotientAddGroup.eq_zero_iff _).2 hz, map_zero, eq_comm, map_eq_zero_iff _ hinj,
      latticePoint_eq_zero_iff] at hq
    exact L.ω₁_div_two_notMem_lattice hq
  obtain ⟨f, g, hf, -, hev⟩ := hξ z₀ hz₀
  let ψ : ℂ →+ (latticeCurve L).toAffine.Point :=
    (variableChangePointEquiv C h).symm.toAddMonoidHom.comp
      (ξ.toAddMonoidHom.comp (QuotientAddGroup.mk' Λ))
  have hψ : ∀ z : ℂ, variableChangePoint C h (ψ z) = ξ z := fun z =>
    (variableChangePointEquiv C h).apply_symm_apply _
  obtain ⟨α, hα⟩ := exists_eq_latticePoint_mul ψ (z₀ := z₀)
    (F := fun w => (f w - C.r) / (C.u : ℂ) ^ 2) (by fun_prop) (by
      filter_upwards [hev] with w ⟨hw, e⟩
      rw [← hψ] at e
      rcases hP : ψ w with _ | ⟨x, y, hxy⟩
      · rw [hP] at e
        exact (Affine.Point.some_ne_zero _ (e.symm.trans (map_zero _))).elim
      · rw [hP, variableChangePoint_some, Affine.Point.some.injEq] at e
        obtain rfl : x = (f w - C.r) / (C.u : ℂ) ^ 2 := by
          rw [← e.1]; field_simp; ring
        exact ⟨y, hxy, rfl⟩)
  have hΛ : ∀ z, z ∈ Λ ↔ α * z ∈ L.lattice := fun z => by
    rw [← latticePoint_eq_zero_iff, ← hα, ← map_eq_zero_iff _ hinj, hψ, ξ.map_eq_zero_iff,
      QuotientAddGroup.eq_zero_iff]
  refine ⟨α, ?_, hΛ, fun z => by rw [← hα, hψ]⟩
  rintro rfl
  exact hz₀ ((hΛ _).2 (by simp))

theorem exists_isAnalyticIso (h : C • X = latticeCurve L) {α : ℂ} (hα : α ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ α * z ∈ L.lattice) :
    ∃ ξ : (ℂ ⧸ Λ) ≃+ X.toAffine.Point, IsAnalyticIso ξ ∧
      ∀ z : ℂ, ξ z = variableChangePoint C h (latticePoint L (α * z)) := by
  let φ : ℂ →+ X.toAffine.Point :=
    (variableChangePoint C h).comp ((latticePointHom L).comp (AddMonoidHom.mulLeft α))
  have hφ : ∀ z, φ z = variableChangePoint C h (latticePoint L (α * z)) := fun _ => rfl
  have hker : Λ = φ.ker := by
    ext z
    rw [AddMonoidHom.mem_ker, hφ, map_eq_zero_iff _ (variableChangePoint_bijective C h).1,
      latticePoint_eq_zero_iff, hΛ]
  have hs : Function.Surjective φ :=
    (variableChangePoint_bijective C h).2.comp
      ((latticePoint_surjective L).comp (mul_left_surjective₀ hα))
  refine ⟨(QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hs), fun z hz => ?_, fun z => rfl⟩
  have hz' : α * z ∉ L.lattice := (hΛ z).not.1 hz
  have hP : AnalyticAt ℂ (fun w => L.weierstrassP (α * w)) z :=
    (L.analyticOnNhd_weierstrassP _ hz').comp_of_eq (f := fun w => α * w) (by fun_prop) rfl
  have hP' : AnalyticAt ℂ (fun w => L.derivWeierstrassP (α * w)) z :=
    (L.analyticOnNhd_derivWeierstrassP _ hz').comp_of_eq (f := fun w => α * w) (by fun_prop) rfl
  refine ⟨fun w => (C.u : ℂ) ^ 2 * L.weierstrassP (α * w) + C.r,
    fun w => (C.u : ℂ) ^ 3 * (L.derivWeierstrassP (α * w) / 2) +
      (C.u : ℂ) ^ 2 * C.s * L.weierstrassP (α * w) + C.t, by fun_prop, by fun_prop, ?_⟩
  filter_upwards [(continuous_const_mul α).continuousAt.eventually
    (eventually_notMem_periodLattice L hz')] with w hw
  change ∃ h, φ w = _
  rw [hφ, latticePoint_of_notMem L hw, variableChangePoint_some]
  exact ⟨_, rfl⟩

theorem eq_zero_of_forall_div_mem {c : ℂ} (h : ∀ n : ℕ, c / n ∈ L.lattice) : c = 0 := by
  obtain ⟨n, hn, hn0⟩ := (((tendsto_const_div_atTop_nhds_zero_nat c).eventually
    (L.compl_lattice_sdiff_singleton_mem_nhds 0)).and (eventually_gt_atTop 0)).exists
  by_contra hc
  exact hn ⟨h n, div_ne_zero hc (by exact_mod_cast hn0.ne')⟩

theorem IsAnalyticIso.ext [X.IsElliptic] {ξ ξ' : (ℂ ⧸ Λ) ≃+ X.toAffine.Point}
    (hξ : IsAnalyticIso ξ) (hξ' : IsAnalyticIso ξ')
    (e : ∀ n : ℕ, ξ ((n : ℂ)⁻¹ : ℂ) = ξ' ((n : ℂ)⁻¹ : ℂ)) : ξ = ξ' := by
  obtain ⟨L, C, h⟩ := exists_variableChange_eq_latticeCurve X
  obtain ⟨α, -, -, hα⟩ := hξ.exists_mul h
  obtain ⟨β, -, -, hβ⟩ := hξ'.exists_mul h
  obtain rfl : α = β := sub_eq_zero.1 <| eq_zero_of_forall_div_mem (L := L) fun n => by
    have := e n
    rw [hα, hβ, (variableChangePoint_bijective C h).1.eq_iff, latticePoint_eq_iff] at this
    rwa [div_eq_mul_inv, sub_mul]
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [hα, hβ]

theorem mapPoint_variableChangePoint {Y Y' : WeierstrassCurve ℂ} (σ : ℂ →+* ℂ) (h : C • X = Y)
    (h' : C.map σ • X.map σ = Y') {s : Y.toAffine.Point ≃+ Y'.toAffine.Point}
    (hs : ∀ x y h, ∃ h', s (.some x y h) = .some (σ x) (σ y) h') (P : Y.toAffine.Point) :
    mapPoint X σ (variableChangePoint C h P) = variableChangePoint (C.map σ) h' (s P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · change mapPoint X σ (variableChangePoint C h 0) = variableChangePoint (C.map σ) h' (s 0)
    simp
  · obtain ⟨h'', e⟩ := hs x y hP
    rw [e, variableChangePoint_some, variableChangePoint_some]
    change Affine.Point.some _ _ _ = _
    rw [Affine.Point.some.injEq]
    simp [VariableChange.map]

end Analytic

section Ideals

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

omit [NumberField K] in
theorem mem_idealSub {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {z : ℂ} :
    z ∈ idealSub 𝔞 ↔ ∃ x ∈ 𝔞, algebraMap K ℂ x = z := Iff.rfl

omit [NumberField K] in
theorem algebraMap_mem_idealSub {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {x : K} :
    algebraMap K ℂ x ∈ idealSub 𝔞 ↔ x ∈ 𝔞 :=
  ⟨fun ⟨_, hy, e⟩ => (algebraMap K ℂ).injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [NumberField K] in
@[simp] theorem torsionIncl_mk (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (x : K) :
    torsionIncl 𝔞 (Submodule.Quotient.mk x) = (algebraMap K ℂ x : ℂ) := rfl


omit [Algebra K ℂ] in
theorem exists_natCast_mul_mem {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0) (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K) * x ∈ 𝔞 := by
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger h𝔞
  obtain ⟨r, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b * c}))
  refine ⟨Ideal.absNorm (Ideal.span {b * c}), by simp [hb0, hc0], ?_⟩
  have := (𝔞 : Submodule (𝓞 K) K).smul_mem (e * r) hc
  rw [← map_natCast (algebraMap (𝓞 K) K), ← he]
  rw [← FractionalIdeal.mem_coe]
  convert this using 1
  simp only [Algebra.smul_def, map_mul]
  field_simp


omit [NumberField K] in
theorem exists_eq_of_natCast_mul_mem {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : (n : ℂ) * z ∈ idealSub 𝔞) : ∃ x : K, algebraMap K ℂ x = z := by
  obtain ⟨x, -, e⟩ := mem_idealSub.1 hz
  refine ⟨x / n, ?_⟩
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [map_div₀, e, map_natCast]
  field_simp

theorem transports_of_exists {σ : ℂ ≃ₐ[K] ℂ} {t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ}
    {X : WeierstrassCurve ℂ} [X.IsElliptic] {𝔞 𝔟 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0)
    (h𝔟 : 𝔟 = t⁻¹ • 𝔞) {ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point}
    {ξ' : (ℂ ⧸ idealSub 𝔟) ≃+ (X.map (σ : ℂ →+* ℂ)).toAffine.Point} (h' : IsAnalyticIso ξ')
    (h : ∀ x, mapPoint X (σ : ℂ →+* ℂ) (ξ (torsionIncl 𝔞 x)) =
      ξ' (torsionIncl 𝔟 (mulEquiv t⁻¹ h𝔞 h𝔟 x))) : Transports σ t h𝔞 ξ := by
  subst h𝔟
  refine ⟨ξ', ⟨h', h⟩, fun η hη => hη.1.ext h' fun n => ?_⟩
  obtain ⟨x, hx⟩ := (mulEquiv t⁻¹ h𝔞 rfl).surjective (Submodule.Quotient.mk (n : K)⁻¹)
  have := (hη.2 x).symm.trans (h x)
  rwa [hx, torsionIncl_mk, map_inv₀, map_natCast] at this

omit [Algebra K ℂ] in
theorem exists_ne_intCast (h2 : Module.finrank ℚ K = 2) : ∃ s : 𝓞 K, ∀ a : ℤ, s ≠ a := by
  by_contra! h
  have h1 : Module.finrank ℤ (𝓞 K) ≤ Module.finrank ℤ ℤ :=
    LinearMap.finrank_le_finrank_of_surjective (f := Algebra.linearMap ℤ (𝓞 K))
      fun s => (h s).imp fun a e => by simpa using e.symm
  rw [RingOfIntegers.rank, h2, Module.finrank_self] at h1
  omega

theorem exists_transports (h2 : Module.finrank ℚ K = 2) (σ : ℂ ≃ₐ[K] ℂ)
    {X : WeierstrassCurve ℂ} [X.IsElliptic] {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h𝔞 : 𝔞 ≠ 0)
    {ξ : (ℂ ⧸ idealSub 𝔞) ≃+ X.toAffine.Point} (hξ : IsAnalyticIso ξ) :
    ∃ t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ, Transports σ t h𝔞 ξ := by
  obtain ⟨L, C, h⟩ := exists_variableChange_eq_latticeCurve X
  obtain ⟨α, hα0, hα, hξα⟩ := hξ.exists_mul h
  obtain ⟨L', g2, g3⟩ := CMRam.exists_conj_lattice σ.toRingEquiv L
  obtain ⟨s, hs, hc⟩ := exists_conjEquiv g2 g3
  let f : 𝓞 K →+* ℂ := (algebraMap K ℂ).comp (algebraMap (𝓞 K) K)
  have hst : ∀ r : 𝓞 K, ∀ l ∈ L.lattice, f r * l ∈ L.lattice := fun r l hl => by
    obtain ⟨x, hx, e⟩ := mem_idealSub.1 ((hα (l / α)).2 (by rwa [mul_div_cancel₀ _ hα0]))
    have := (hα _).1 (algebraMap_mem_idealSub.2 ((𝔞 : Submodule (𝓞 K) K).smul_mem r hx))
    rw [Algebra.smul_def, map_mul, e] at this
    convert this using 1
    simp only [f, RingHom.comp_apply]
    field_simp
  have hmul : ∀ (r : 𝓞 K) {u u' : ℂ}, IsConj L L' σ.toRingEquiv u u' →
      IsConj L L' σ.toRingEquiv (f r * u) (f r * u') := fun r u u' huu => by
    have := huu.mul g2 g3 (hst r)
    rwa [show σ.toRingEquiv (f r) = f r from σ.commutes _] at this
  have hmem : ∀ {u u' : ℂ}, IsConj L L' σ.toRingEquiv u u' → (u ∈ L.lattice ↔ u' ∈ L'.lattice) :=
    fun huu => by simpa using huu.nsmul_mem_iff g2 g3 1
  obtain ⟨r₀, hr₀⟩ := exists_ne_intCast h2
  obtain ⟨I, δ, hI, hδ, hIδ⟩ := ConjCurve.exists_ideal f L'.lattice.toAddSubgroup L'.ω₁ L'.ω₂
    (by simpa using L'.indep.ne_zero 0) (fun z => PeriodPair.mem_lattice)
    (fun r z hz => (hmem (hmul r (.inl ⟨zero_mem _, hz⟩))).1 (by simp)) r₀
    (fun a e => hr₀ a (IsFractionRing.injective (𝓞 K) K ((algebraMap K ℂ).injective
      (e.trans (map_intCast f a).symm))))
  let 𝔟 : FractionalIdeal (𝓞 K)⁰ K := I
  have h𝔟 : 𝔟 ≠ 0 := by simpa [𝔟] using hI
  have hδ' : ∀ z, z ∈ idealSub 𝔟 ↔ δ * z ∈ L'.lattice := fun z => by
    rw [← Submodule.mem_toAddSubgroup, hIδ, mem_idealSub]
    constructor
    · rintro ⟨_, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, e⟩
      exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩, (mul_left_cancel₀ hδ e).symm⟩
  let R : K → K → Prop := fun x y =>
    IsConj L L' σ.toRingEquiv (α * algebraMap K ℂ x) (δ * algebraMap K ℂ y)
  have Rtot : ∀ x, ∃ y, R x y := fun x => by
    obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L (α * algebraMap K ℂ x)))
    have hw' := (hc _ _).2 hw.symm
    obtain ⟨n, hn, hx⟩ := exists_natCast_mul_mem h𝔞 x
    have h1 := (hα _).1 (algebraMap_mem_idealSub.2 hx)
    rw [map_mul, map_natCast, mul_left_comm, hw'.nsmul_mem_iff g2 g3] at h1
    obtain ⟨y, hy⟩ := exists_eq_of_natCast_mul_mem (𝔞 := 𝔟) hn (z := w / δ)
      ((hδ' _).2 (by convert h1 using 1; field_simp))
    exact ⟨y, by simp only [R]; rwa [hy, mul_div_cancel₀ _ hδ]⟩
  have Rsurj : ∀ y, ∃ x, R x y := fun y => by
    obtain ⟨w, hw⟩ := latticePoint_surjective L (s.symm (latticePoint L' (δ * algebraMap K ℂ y)))
    have hw' := (hc w _).2 (by rw [hw, s.apply_symm_apply])
    obtain ⟨n, hn, hy⟩ := exists_natCast_mul_mem h𝔟 y
    have h1 := (hδ' _).1 (algebraMap_mem_idealSub.2 hy)
    rw [map_mul, map_natCast, mul_left_comm, ← hw'.nsmul_mem_iff g2 g3] at h1
    obtain ⟨x, hx⟩ := exists_eq_of_natCast_mul_mem (𝔞 := 𝔞) hn (z := w / α)
      ((hα _).2 (by convert h1 using 1; field_simp))
    exact ⟨x, by simp only [R]; rwa [hx, mul_div_cancel₀ _ hα0]⟩
  have Radd : ∀ {x y x' y'}, R x y → R x' y' → R (x + x') (y + y') := fun a b => by
    simpa only [R, map_add (f := _), mul_add] using a.add g2 g3 b
  have Rsmul : ∀ (r : 𝓞 K) {x y}, R x y → R (r • x) (r • y) := fun r x y a => by
    have := hmul r a
    rw [mul_left_comm, mul_left_comm (f r)] at this
    simp only [R, Algebra.smul_def, map_mul]
    exact this
  have Rmem : ∀ {x y}, R x y → (x ∈ 𝔞 ↔ y ∈ 𝔟) := fun a => by
    rw [← algebraMap_mem_idealSub, ← algebraMap_mem_idealSub, hα, hδ', hmem a]
  have Runiq : ∀ {x y y'}, R x y → R x y' → (Submodule.Quotient.mk y :
      K ⧸ (𝔟 : Submodule (𝓞 K) K)) = Submodule.Quotient.mk y' := fun a b => by
    have := Rmem (Radd a (Rsmul (-1) b))
    rw [neg_one_smul, neg_one_smul, add_neg_cancel, ← sub_eq_add_neg] at this
    exact (Submodule.Quotient.eq _).2 (this.1 (FractionalIdeal.zero_mem _))
  choose F hF using Rtot
  let Φ : K →ₗ[𝓞 K] K ⧸ (𝔟 : Submodule (𝓞 K) K) :=
    { toFun := fun x => Submodule.Quotient.mk (F x)
      map_add' := fun x y => Runiq (hF _) (Radd (hF x) (hF y))
      map_smul' := fun r x => Runiq (hF _) (Rsmul r (hF x)) }
  have hker : (𝔞 : Submodule (𝓞 K) K) = LinearMap.ker Φ := by
    ext x
    exact (Rmem (hF x)).trans (Submodule.Quotient.mk_eq_zero _).symm
  have hΦ : Function.Surjective Φ := fun q => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx⟩ := Rsurj y
    exact ⟨x, Runiq (hF x) hx⟩
  obtain ⟨u, ⟨hu, hφ⟩, -⟩ := existsUnique_mulEquiv h𝔞
    ((Submodule.quotEquivOfEq _ _ hker).trans (Φ.quotKerEquivOfSurjective hΦ))
  have h' : C.map (σ : ℂ →+* ℂ) • X.map (σ : ℂ →+* ℂ) = latticeCurve L' := by
    rw [map_variableChange, h]
    simp [latticeCurve, WeierstrassCurve.map, g2, g3, map_ofNat]
  obtain ⟨ξ', hξ', e'⟩ := exists_isAnalyticIso h' hδ hδ'
  obtain ⟨t, rfl⟩ : ∃ t, u = t⁻¹ := ⟨u⁻¹, (inv_inv u).symm⟩
  refine ⟨t, transports_of_exists h𝔞 hu hξ' fun q => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← hφ]
  change _ = ξ' (torsionIncl 𝔟 (Submodule.Quotient.mk (F x)))
  rw [torsionIncl_mk, torsionIncl_mk, hξα, e', mapPoint_variableChangePoint _ h h' hs,
    (hc _ _).1 (hF x)]


omit [Algebra K ℂ] in
theorem finitePart_inr (t : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) :
    finitePart (K := K) (Units.map (MonoidHom.inr (InfiniteAdeleRing K) _) t) = t :=
  Units.ext rfl

end Ideals

end GlobalTheory.EllipticCM
