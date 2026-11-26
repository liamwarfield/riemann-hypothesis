module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalModularFormCuspForm
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.FinDim

open Asymptotics Filter Topology Function

theorem bigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (hc : ∀ n < m, (qExpansion h f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam h τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := hc i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty hh
  have h2 : (fun τ : ℍ => g (Periodic.qParam h τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam h τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne'] at hτ
  rw [hτ]; simp

theorem coeff_eq_zero_of_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    rw [← hj] at hlt
    have hjm : j < m := by exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp hj.symm
    have ht := qParam_tendsto_atImInfty (h := 1) one_pos
    have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty]
        fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j) := by
      have h3 := (isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h
      refine h3.congr' ?_ ?_
      · filter_upwards [ht.eventually hfg] with τ hτ
        rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        rw [hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      · refine Eventually.of_forall fun τ => ?_
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        simp only
        rw [pow_sub₀ _ hq hjm.le, mul_comm]
    have h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0) := by
      have := ht.pow (m - j)
      rwa [zero_pow (by omega)] at this
    exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at h1
  intro n hn
  rw [qExpansion_coeff, h1 n hn, mul_zero]

theorem qParam_pow_bigO {h : ℝ} (hh : 0 < h) {m M : ℕ} (hm : (M : ℝ) * h ≤ m) :
    (fun τ : ℍ => Periodic.qParam h τ ^ m) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ M := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [one_mul, norm_pow, norm_pow, Periodic.norm_qParam, Periodic.norm_qParam, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul, Real.exp_le_exp]
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have key : (M : ℝ) * (τ : ℂ).im ≤ m * (τ : ℂ).im / h := by
    rw [le_div_iff₀ hh]; nlinarith
  have e1 : (m : ℝ) * (-2 * Real.pi * (τ : ℂ).im / h) = -2 * Real.pi * (m * (τ : ℂ).im / h) := by ring
  have e2 : (M : ℝ) * (-2 * Real.pi * (τ : ℂ).im / 1) = -2 * Real.pi * (M * (τ : ℂ).im) := by ring
  rw [e1, e2]
  nlinarith [Real.pi_pos]

theorem norm_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))
  have hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ),
      SlashInvariantForm.quotientFunc (k := k) f q =O[atImInfty] fun _ => (1 : ℂ) := by
    refine Quotient.forall.mpr fun ⟨r, hr⟩ => ?_
    have hc : IsCusp OnePoint.infty 𝒮ℒ := Fact.out
    have := (ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty)
      (by simpa using hc.of_isFiniteRelIndex_conj hr)
    rw [OnePoint.isBoundedAt_infty_iff] at this
    have h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ) := this
    refine IsBigO.trans h2 ?_
    exact IsBigO.of_bound 1 (by simp)
  have h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)),
      SlashInvariantForm.quotientFunc (k := k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by
    have := IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)
    simpa [Finset.prod_fn] using this
  have h2 := (isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1
  simp only [mul_one] at h2
  refine h2.congr_left fun τ => ?_
  have h3 := congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q)
    (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ
  rw [ModularForm.coe_norm]
  have h4 : SlashInvariantForm.quotientFunc (k := k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp
  rw [h4, Pi.mul_apply] at h3
  convert h3

theorem sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion h f).coeff n = 0) → f = 0 := by
  set M := (k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1
  refine ⟨⌈(M : ℝ) * h⌉₊, fun f hf => ?_⟩
  have h1 := coeff_eq_zero_of_bigO one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) M
    ((norm_bigO f).trans ((bigO_qParam_pow hh hΓ f _ hf).trans (qParam_pow_bigO hh (Nat.le_ceil _))))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

def coeffMap {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ)
    (m : ℕ) : ModularForm Γ k →ₗ[ℂ] (Fin m → ℂ) where
  toFun f n := (qExpansion h f).coeff n
  map_add' f g := by
    funext n
    simp only [Pi.add_apply]
    rw [ModularForm.coe_add, ModularForm.qExpansion_add hh hΓ f g, map_add (f := _)]
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [ModularForm.coe_smul, ModularForm.qExpansion_smul hh hΓ c f, PowerSeries.coeff_smul, smul_eq_mul]

theorem finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne]
    (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  obtain ⟨m, hm⟩ := sturm Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k
  refine Module.Finite.of_injective (coeffMap Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k m) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  exact hm f fun n hn => congr_fun hf ⟨n, hn⟩

end GlobalTheory.HeckeFamilyMatrices.FinDim


open GlobalTheory.HeckeFamilyMatrices.FinDim in
theorem GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm :
    ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro Γ k hΓ
  have h1 := finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) k
  refine ⟨h1, ?_⟩
  haveI := h1
  exact Module.Finite.equiv (CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) k).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem finiteDimensional_of_Gamma_le :
    ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro M Γ k hM hle
  exact GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm Γ k (finiteIndex_of_Gamma_le hM hle)

end GlobalTheory.OddFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLeStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | exact GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | (intros; apply GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesToSmallerOddWeightOfLeadingCoeffMatrixDet
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCusps
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCusps
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem discriminant_slash_specialLinearGroup (x : SL(2, ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] x) = ModularForm.discriminant :=
  (isCF_coe_top CuspForm.discriminant).1 x (Subgroup.mem_top x)

theorem exists_eq_discriminant_mul (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ) (hH : IsMF Γ K H)
    (hdec : ∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  have hsl : ∀ x : SL(2, ℤ), (H / ModularForm.discriminant) ∣[K - 12] x =
      (H ∣[K] x) / ModularForm.discriminant := by
    intro x
    have := ModularForm.div_slash_SL2 K 12 x H ModularForm.discriminant
    rw [discriminant_slash_specialLinearGroup] at this
    exact this
  refine ⟨H / ModularForm.discriminant, ⟨fun γ hγ => ?_, ?_, fun x => ?_⟩, ?_⟩
  · rw [hsl, hH.1 γ hγ]
  · exact hH.2.1.div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero
  · rw [hsl, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO ((hdec x).trans ModularForm.exp_isBigO_discriminant)).isBigO_one ℝ
  · ext τ
    simp [mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCuspsStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps : ∀ (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ), IsMF Γ K H → (∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) → ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  first | exact @GlobalTheory.exists_eq_discriminant_mul | exact GlobalTheory.exists_eq_discriminant_mul | (intros; apply GlobalTheory.exists_eq_discriminant_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecay
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem levelOne_form_one_add_expDecay :
    ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧
      (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro d hd hev
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ d)
  have hk : 3 ≤ k := by omega
  have hk2 : Even k := by simpa [Int.even_coe_nat] using hev
  let f : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.E hk
  refine ⟨f, isMF_coe_top f, ?_⟩
  have h0 : valueAtInfty (f : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  have h := exp_decay_sub_atImInfty one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  rw [h0] at h
  simpa using h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecayStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelOne_form_one_add_expDecay : ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧ (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.levelOne_form_one_add_expDecay | exact GlobalTheory.levelOne_form_one_add_expDecay | (intros; apply GlobalTheory.levelOne_form_one_add_expDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesToSmallerOddWeightOfLeadingCoeffMatrixDet
open UpperHalfPlane Filter GlobalTheory.OddFrame Asymptotics
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

private theorem slash_finset_sum {ι : Type*} (t : Finset ι) (k : ℤ) (f : ι → ℍ → ℂ) (x : SL(2, ℤ)) :
    (∑ i ∈ t, f i) ∣[k] x = ∑ i ∈ t, (f i) ∣[k] x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

private theorem tendsto_exp_neg_im :
    Tendsto (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) atImInfty (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  exact h.const_mul_atTop_of_neg (by linarith [Real.pi_pos])

theorem reduces_of_det_leadM_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s →
    (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det = 0 → Reduces Γ w F := by
  classical
  intro M Γ r s w F hM hΓ hs hF hdet
  obtain ⟨c, hc, hcv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hT := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  have hb : ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → ∑ j, c j * co M (w j) (F j) x n = 0 := by
    refine GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero M Γ r s (fun x n => ∑ j, c j * co M (w j) (F j) x n) hM hs ?_ ?_ ?_ ?_
    · intro x n
      simp only [fun j => (hT j).1 x n, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro γ hγ x n
      simp only [fun j => (hT j).2.1 γ hγ x n]
    · intro x n
      simp only [fun j => (hT j).2.2 (hF j).1 x n, mul_neg, Finset.sum_neg_distrib]
    · intro i
      have := congrFun hcv i
      simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply, Pi.zero_apply, Finset.sum_mul] at this
      rw [Finset.sum_comm, ← this]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hO : ∀ x : SL(2, ℤ), (fun τ : ℍ => ∑ j, c j * (F j ∣[w j] x) τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 := IsBigO.sum (s := Finset.univ) fun j _ =>
      (GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 x).const_mul_left (c j)
    refine h1.congr_left fun τ => ?_
    simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm, sub_eq_self]
    refine Finset.sum_eq_zero fun n hn => ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hb x n (Finset.mem_range.mp hn), zero_mul]
  have hne : (Finset.univ.filter fun j => c j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    exact ⟨j, by simpa using hj⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image _ w hne
  have hc₀ : c j₀ ≠ 0 := by simpa using hj₀
  have he : ∀ j, ∃ e : ℍ → ℂ, IsMF ⊤ (w j₀ - w j + 4) e ∧
      (fun τ : ℍ => e τ - c j) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro j
    by_cases hj : c j = 0
    · exact ⟨0, IsMF.zero _ _, by simp [hj, isBigO_zero]⟩
    · have hle : w j ≤ w j₀ := hmax j (by simpa using hj)
      obtain ⟨e, h1, h2⟩ := GlobalTheory.T.exists_levelOne_form_one_add_expDecay (w j₀ - w j + 4) (by omega)
        (((hF j₀).1.sub_odd (hF j).1).add (by decide))
      refine ⟨c j • e, h1.smul _, (h2.const_mul_left (c j)).congr_left fun τ => ?_⟩
      simp [mul_sub]
  choose e heMF heO using he
  have hH : IsMF Γ (w j₀ + 4) (∑ j, e j * F j) :=
    IsMF.sum _ fun j _ => ((heMF j).mono le_top).mul (hF j).2 (by ring)
  have hHx : ∀ x : SL(2, ℤ), (∑ j, e j * F j) ∣[w j₀ + 4] x = ∑ j, e j * (F j ∣[w j] x) := by
    intro x
    rw [slash_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : w j₀ + 4 = (w j₀ - w j + 4) + w j := by ring
    rw [this, ModularForm.mul_slash_SL2, (heMF j).slash_top]
  have hHO : ∀ x : SL(2, ℤ), ((∑ j, e j * F j) ∣[w j₀ + 4] x) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 : (fun τ : ℍ => ∑ j, (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
        fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      have h2 : ∀ j, (fun τ : ℍ => (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
          fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
        intro j
        have hb' : (F j ∣[w j] x) =O[atImInfty] (fun _ => (1 : ℝ)) := (hF j).2.2.2 x
        simpa only [mul_one] using (heO j).mul hb'
      exact (IsBigO.sum (s := Finset.univ) fun j _ => h2 j).congr_left fun τ => Finset.sum_apply _ _ _
    rw [hHx]
    refine (h1.add (hO x)).congr_left fun τ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by simp; ring
  obtain ⟨G, hG, hHG⟩ := GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps Γ _ _ hH hHO
  have hΔ : IsMF ⊤ 12 ModularForm.discriminant := (isCF_coe_top CuspForm.discriminant).isMF
  refine ⟨j₀, w j₀ + 4 - 12, G, ModularForm.discriminant, e, by omega, ?_, hG,
    fun j => (heMF j).2.1, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := (hF j₀).1
    exact ⟨m - 4, by omega⟩
  · intro h0
    have h1 := (heO j₀).trans_tendsto tendsto_exp_neg_im
    rw [h0] at h1
    simp only [Pi.zero_apply, zero_sub] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    exact hc₀ (neg_eq_zero.mp this.symm)
  · intro x τ
    have h1 := hHx x
    have h2 : w j₀ + 4 = 12 + (w j₀ + 4 - 12) := by ring
    rw [hHG, h2, ModularForm.mul_slash_SL2, hΔ.slash_top] at h1
    have h3 := congrFun h1 τ
    simpa [Finset.sum_apply] using h3

end GlobalTheory.OddFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesToSmallerOddWeightOfLeadingCoeffMatrixDetStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducesToSmallerOddWeight_of_leadingCoeffMatrix_det_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det = 0 → Reduces Γ w F := by
  first | exact @GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero | exact GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero | (intros; apply GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCube
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCube
noncomputable section

namespace GlobalTheory.DerExt

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {ι : Type} [Fintype ι]

def D0 (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * d (tr (v k * x))

def phi (D : Ω → Ω) (x y : Ω) : Ω := D (x * y) - x * D y - y * D x

def psi (u v : ι → Ω) (D : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * phi D (v k) x

theorem phi_comm (D : Ω → Ω) (x y : Ω) : phi D x y = phi D y x := by
  unfold phi; rw [mul_comm x y]; ring

theorem phi_one (D : Ω → Ω) (y : Ω) : phi D 1 y = -(y * D 1) := by
  unfold phi; simp

theorem phi_ident (D : Ω → Ω) (w x y : Ω) :
    w * phi D x y - phi D (w * x) y + phi D w (x * y) - y * phi D w x = 0 := by
  unfold phi; rw [show w * x * y = w * (x * y) by ring]; ring

variable {B C : Subalgebra (O0 p) Ω} {u v : ι → Ω} {tr : Ω → Ω} {d : Ω → Ω}

private theorem isInt_congr {x y : Ω} (hx : IsInt (p := p) x) (h : y = x) :
    IsInt (p := p) y := h ▸ hx

theorem traceDerivationFirstApprox_add_isInt (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (D0 u v tr d (x + y) - D0 u v tr d x - D0 u v tr d y) := by
  obtain ⟨_, hCi, hu, hv, htr, hadd, -⟩ := h
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
    (hd.1 _ (htr _ (C.mul_mem (hv k) hx)) _ (htr _ (C.mul_mem (hv k) hy)))) ?_
  simp only [D0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, hadd _ (C.mul_mem (hv k) hx) _ (C.mul_mem (hv k) hy)]; ring

theorem traceDerivationFirstApprox_mul_left_isInt (h : DualData B C u v tr) (hd : IsDer B d) {b x : Ω} (hb : b ∈ B) (hx : x ∈ C) :
    IsInt (p := p) (D0 u v tr d (b * x) - b * D0 u v tr d x - p * x * d b) := by
  obtain ⟨_, hCi, hu, hv, htr, -, hlin, hdual, -⟩ := h
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
    (hd.2.1 b hb _ (htr _ (C.mul_mem (hv k) hx)))) ?_
  rw [← hdual x hx]
  simp only [D0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show v k * (b * x) = b * (v k * x) by ring, hlin b hb _ (C.mul_mem (hv k) hx)]; ring

theorem phi_add (h : DualData B C u v tr) (hd : IsDer B d) {x x' y : Ω} (hx : x ∈ C) (hx' : x' ∈ C)
    (hy : y ∈ C) :
    IsInt (p := p) (phi (D0 u v tr d) (x + x') y - phi (D0 u v tr d) x y - phi (D0 u v tr d) x' y) := by
  refine isInt_congr (IsIntegral.sub (traceDerivationFirstApprox_add_isInt h hd (C.mul_mem hx hy) (C.mul_mem hx' hy))
    (IsIntegral.mul (h.2.1 y hy) (traceDerivationFirstApprox_add_isInt h hd hx hx'))) ?_
  simp only [phi, add_mul]; ring

theorem phi_bmul (h : DualData B C u v tr) (hd : IsDer B d) {b x y : Ω} (hb : b ∈ B) (hx : x ∈ C)
    (hy : y ∈ C) :
    IsInt (p := p) (phi (D0 u v tr d) (b * x) y - b * phi (D0 u v tr d) x y) := by
  refine isInt_congr (IsIntegral.sub (traceDerivationFirstApprox_mul_left_isInt h hd hb (C.mul_mem hx hy))
    (IsIntegral.mul (h.2.1 y hy) (traceDerivationFirstApprox_mul_left_isInt h hd hb hx))) ?_
  simp only [phi]; rw [show b * x * y = b * (x * y) by ring]; ring

theorem lin_sum (h : DualData B C u v tr) (f : Ω → Ω)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, IsInt (p := p) (f (x + y) - f x - f y))
    (hlin : ∀ b ∈ B, ∀ x ∈ C, IsInt (p := p) (f (b * x) - b * f x))
    {κ : Type} (s : Finset κ) (w b : κ → Ω) (hw : ∀ i, w i ∈ C) (hb : ∀ i, b i ∈ B) :
    IsInt (p := p) (f (∑ i ∈ s, w i * b i) - ∑ i ∈ s, b i * f (w i)) := by
  classical
  have hBC := h.1
  induction s using Finset.induction_on with
  | empty =>
    simpa using hlin 0 B.zero_mem 0 C.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : ∑ i ∈ s, w i * b i ∈ C := C.sum_mem fun i _ => C.mul_mem (hw i) (hBC (hb i))
    have h1 := hadd _ (C.mul_mem (hw a) (hBC (hb a))) _ hS
    have h2 := hlin (b a) (hb a) (w a) (hw a)
    rw [mul_comm (b a) (w a)] at h2
    exact isInt_congr (IsIntegral.add h1 (IsIntegral.add h2 ih)) (by ring)

theorem sum_swap_eq (h : DualData B C u v tr) (D : Ω → Ω) {x : Ω} (hx : x ∈ C) (y : Ω) :
    ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y = p * x * psi u v D y := by
  obtain ⟨_, -, hu, -, -, -, -, hdual, -⟩ := h
  calc ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y
      = ∑ k, ∑ l, u k * tr (v k * (x * u l)) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show u l * (v k * x) = v k * (x * u l) by ring]; ring
    _ = ∑ l, ∑ k, u k * tr (v k * (x * u l)) * phi D (v l) y := Finset.sum_comm
    _ = ∑ l, (∑ k, u k * tr (v k * (x * u l))) * phi D (v l) y := by
        simp only [Finset.sum_mul]
    _ = ∑ l, p * (x * u l) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hdual _ (C.mul_mem hx (hu l))]
    _ = p * x * psi u v D y := by
        simp only [psi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem S_congr (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (p * ∑ k, u k * phi (D0 u v tr d) (v k * x) y - p * x * psi u v (D0 u v tr d) y) := by
  have hBC := h.1
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have htr := h.2.2.2.2.1
  have hdual2 := h.2.2.2.2.2.2.2.2.1
  have hpB : (p : Ω) ∈ B := natCast_mem B p
  have key : ∀ k, IsInt (p := p) (u k * (p * phi (D0 u v tr d) (v k * x) y -
      ∑ l, tr (u l * (v k * x)) * phi (D0 u v tr d) (v l) y)) := by
    intro k
    have hz : v k * x ∈ C := C.mul_mem (hv k) hx
    have ha := phi_bmul h hd hpB hz hy
    have hb := lin_sum h (fun z => phi (D0 u v tr d) z y)
      (fun a ha b hb => phi_add h hd ha hb hy) (fun b hb a ha => phi_bmul h hd hb ha hy)
      Finset.univ v (fun l => tr (u l * (v k * x))) hv
      (fun l => htr _ (C.mul_mem (hu l) hz))
    rw [hdual2 _ hz] at hb
    exact IsIntegral.mul (hCi _ (hu k)) (isInt_congr (IsIntegral.sub hb ha) (by ring))
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => key k) ?_
  rw [← sum_swap_eq h (D0 u v tr d) hx y, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

def Dext (p : ℕ) (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω :=
  (p : Ω) ^ 2 * D0 u v tr d x + p * psi u v (D0 u v tr d) x

theorem Dext_mul (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (Dext p u v tr d (x * y) - x * Dext p u v tr d y - y * Dext p u v tr d x) := by
  have hsum := h.2.2.2.2.2.2.2.2.2
  have hid : (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
      psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x = 0 := by
    calc (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
          psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x
        = ∑ k, u k * (v k * phi (D0 u v tr d) x y - phi (D0 u v tr d) (v k * x) y +
            phi (D0 u v tr d) (v k) (x * y) - y * phi (D0 u v tr d) (v k) x) := by
          rw [← hsum]
          simp only [psi, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by simp [phi_ident]
  refine isInt_congr (S_congr h hd hx hy) ?_
  simp only [Dext, phi, psi] at hid ⊢
  linear_combination (p : Ω) * hid

theorem Dext_add (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (Dext p u v tr d (x + y) - Dext p u v tr d x - Dext p u v tr d y) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have h1 := traceDerivationFirstApprox_add_isInt h hd hx hy
  have h2 : IsInt (p := p) (∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
      phi (D0 u v tr d) y (v k))) :=
    IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k)) (phi_add h hd hx hy (hv k))
  have hp : IsIntegral (O0 p) (p : Ω) := isIntegral_natCast p
  refine isInt_congr (IsIntegral.add ((hp.pow 2).mul h1) (hp.mul h2)) ?_
  have e : psi u v (D0 u v tr d) (x + y) - psi u v (D0 u v tr d) x - psi u v (D0 u v tr d) y =
      ∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
        phi (D0 u v tr d) y (v k)) := by
    simp only [psi, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) (x + y), phi_comm _ (v k) x, phi_comm _ (v k) y]; ring
  simp only [Dext]
  linear_combination (p : Ω) * e

theorem Dext_B (h : DualData B C u v tr) (hd : IsDer B d) {b : Ω} (hb : b ∈ B) :
    IsInt (p := p) (Dext p u v tr d b - (p : Ω) ^ 3 * d b) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have hsum := h.2.2.2.2.2.2.2.2.2
  have h1 := traceDerivationFirstApprox_mul_left_isInt h hd hb C.one_mem
  rw [mul_one, mul_one] at h1
  have h2 : IsInt (p := p) (psi u v (D0 u v tr d) b + p * b * D0 u v tr d 1) := by
    refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
      (phi_bmul h hd hb C.one_mem (hv k))) ?_
    rw [← hsum]
    simp only [psi, phi_one, mul_one, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) b]; ring
  have hp : IsIntegral (O0 p) (p : Ω) := isIntegral_natCast p
  refine isInt_congr (IsIntegral.add ((hp.pow 2).mul h1) (hp.mul h2)) ?_
  simp only [Dext]; ring

theorem Dext_isDer (h : DualData B C u v tr) (hd : IsDer B d) : IsDer C (Dext p u v tr d) :=
  ⟨fun x hx y hy => Dext_add h hd hx hy, fun x hx y hy => Dext_mul h hd hx hy,
   fun c => isInt_congr (IsIntegral.add (Dext_B h hd (B.algebraMap_mem c))
     (((isIntegral_natCast (R := O0 p) (B := Ω) p).pow 3).mul (hd.2.2 c))) (by ring)⟩

theorem exists_ext : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
    ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt (p := p) (D b - (p : Ω) ^ 3 * d b) := by
  intro p _ Ω _ _ B C ι _ u v tr h d hd
  exact ⟨Dext p u v tr d, Dext_isDer h hd, fun b hb => Dext_B h hd hb⟩

end GlobalTheory.DerExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCubeStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationModIntegral_extension_p_cube : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt (p := p) (D b - (p : Ω) ^ 3 * d b) := by
  first | exact @GlobalTheory.DerExt.exists_ext | exact GlobalTheory.DerExt.exists_ext | (intros; apply GlobalTheory.DerExt.exists_ext <;> assumption)
end
end
