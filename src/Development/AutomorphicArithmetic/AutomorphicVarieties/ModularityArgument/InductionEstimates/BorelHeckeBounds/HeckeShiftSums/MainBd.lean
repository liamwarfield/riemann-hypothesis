module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.GeoRatio
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.FarSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.ContinuousLeviUnipotentPath
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.CtVanish
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.BlkCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.RootDecay
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.DiffBd
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate Pointwise Manifold ContDiff

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump {K : Type} [Field K] [NumberField K] {n : ℕ} {L : Set (ArchMatrix K n)}
    (hL : IsCompact L) (hLu : L ⊆ {x | IsUnit x}) :
    ∃ χ : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ L, χ x = 1) ∧
      tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  obtain ⟨M, hM, hLM, hMu⟩ := exists_compact_between hL Units.isOpen hLu
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := ⊤)
    𝓘(ℝ, ArchMatrix K n) hL.isClosed hLM
  have hsub : tsupport f ⊆ M :=
    closure_minimal (fun x hx => by_contra fun h => hx (h0 x h)) hM.isClosed
  refine ⟨f, f.contMDiff.contDiff, hM.of_isClosed_subset (isClosed_tsupport _) hsub,
    fun x hx => (h1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds, fun x hx => ?_⟩
  obtain ⟨u, rfl⟩ := hMu (hsub hx)
  exact ⟨u, rfl⟩

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {χ : ArchMatrix K n → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχu : tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) :
    (isExpLieAlgebra K n).IsTestFunction
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) := by
  refine ⟨((isExpLieAlgebra K n).isSmoothFun_iff).2 fun g => ?_, ?_⟩
  · refine ContDiff.mul ?_ (((isExpLieAlgebra K n).isSmoothFun_iff).1 hf g)
    have e : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun Y : archLie K n =>
        (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n) := by
      have : (fun Y : archLie K n =>
          (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n)) =
          fun Y : archLie K n => ((g : ArchUnits K n) : ArchMatrix K n) * NormedSpace.exp (Y : ArchMatrix K n) := by
        funext Y
        simp only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
      rw [this]
      exact contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix K n)).comp (archLie K n).subtypeL.contDiff)
    exact Complex.ofRealCLM.contDiff.comp (hχ.comp e)
  · refine HasCompactSupport.intro
      ((isCompact_unitsSupport hχc hχu).image (archGroupEquiv K n).symm.continuous) fun a ha => ?_
    have : ((a : ArchUnits K n) : ArchMatrix K n) ∉ tsupport χ := fun h =>
      ha ⟨(a : ArchUnits K n), h, (archGroupEquiv K n).symm_apply_apply a⟩
    rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {T : Set (archGroup K n)} (hT : IsCompact T) (k : ℕ) (R : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
      ∀ A ∈ T, ‖∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩‖ ≤ c * ∏ i, ‖Y i‖ := by
  set T₀ : Set (ArchUnits K n) := (fun a : archGroup K n => (a : ArchUnits K n)) '' T with hT₀
  have hT₀c : IsCompact T₀ := hT.image continuous_subtype_val
  set T₁ : Set (ArchUnits K n) := (unipBall (K := K) (n := n) (k * R))⁻¹ * T₀ with hT₁
  have hT₁c : IsCompact T₁ := (isCompact_unipBall _).inv.mul hT₀c
  set L : Set (ArchMatrix K n) := (Units.val : ArchUnits K n → ArchMatrix K n) '' T₁ with hLdef
  have hLc : IsCompact L := hT₁c.image Units.continuous_val
  have hLu : L ⊆ {x | IsUnit x} := by
    rintro _ ⟨u, -, rfl⟩
    exact u.isUnit
  obtain ⟨χ, hχ, hχc, hχ1, hχu⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump hLc hLu
  have hκ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test hf hχ hχc hχu
  obtain ⟨B, hB⟩ := exists_norm_altSum_le (contDiff_matExt hκ) (hasCompactSupport_matExt hκ.2) k
  obtain ⟨Rt, hRt⟩ := hT₀c.exists_bound_of_continuousOn
    (Units.continuous_val (M := ArchMatrix K n)).continuousOn
  refine ⟨max B 0 * max Rt 0 ^ k, mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _),
    fun Y hY hR C hC A hA => ?_⟩
  have hAT₀ : (A : ArchUnits K n) ∈ T₀ := ⟨A, hA, rfl⟩
  set v : Fin k → ArchMatrix K n := fun i => -(Y i * ((A : ArchUnits K n) : ArchMatrix K n)) with hv
  have hsum : ∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩ =
      altSum k (matExt K n fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) v
        ((A : ArchUnits K n) : ArchMatrix K n) := by
    rw [altSum_eq_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [← val_inv_mul_eq hY (hC ε) (A : ArchUnits K n), zsmul_eq_mul]
    have hm := matExt_val (K := K) (n := n)
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a)
      ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩
    have hin : (((C ε)⁻¹ * (A : ArchUnits K n) : ArchUnits K n) : ArchMatrix K n) ∈ L :=
      ⟨_, ⟨(C ε)⁻¹, Set.inv_mem_inv.2 (mem_unipBall_of_val_eq hY hR (hC ε)), _, hAT₀, rfl⟩, rfl⟩
    simp only at hm
    rw [hm, hχ1 _ hin, Complex.ofReal_one, one_mul]
  rw [hsum]
  refine (hB v _).trans ?_
  have hA' : ‖((A : ArchUnits K n) : ArchMatrix K n)‖ ≤ max Rt 0 := (hRt _ hAT₀).trans (le_max_left _ _)
  have hprod : ∏ i, ‖v i‖ ≤ (∏ i, ‖Y i‖) * max Rt 0 ^ k := by
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [hv, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
  calc B * ∏ i, ‖v i‖ ≤ max B 0 * ∏ i, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ ≤ max B 0 * ((∏ i, ‖Y i‖) * max Rt 0 ^ k) := mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
    _ = max B 0 * max Rt 0 ^ k * ∏ i, ‖Y i‖ := by ring

private def UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n) (k : ℕ) (R : ℝ)
    (s : Set (G1 K n)) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
    ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
    ∀ w ∈ s, ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split {K : Type} [Field K] [NumberField K] {n : ℕ} {g : G1 K n}
    {u : AdelicGLn.integralFiniteGL K n} (hu : finPart K n (g : AdelicGLn.AdelicGL K n) = u) :
    g = finOne K n u * archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
  have hd : detA K n (infPart K n (g : AdelicGLn.AdelicGL K n)) = 1 :=
    detA_infPart (hu ▸ u.2)
  have hp : (archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) : AdelicGLn.AdelicGL K n) =
      infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
    rw [← retract_infEmb, coe_retractOne]
    have : detModule K n (infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n))) = 1 := hd
    rw [this, map_one, inv_one, mul_one]
  rw [← archimedeanProjection_mul_finiteEmbedding_comm]
  ext1
  rw [Subgroup.coe_mul, hp, coe_finOne, ← hu, infEmb_infPart_mul_finEmb_finPart]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n), IsLeftSmooth a → ∀ (k : ℕ) (R : ℝ), ∃ c : ℝ, ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) → ∀ w : G1 K n,
        ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖ := by
  intro K _ _ n a ha k R
  obtain ⟨hsm, U, hUo, hU⟩ := ha
  set Ω : Set (G1 K n) := (archProj K n '' unipBall (K := K) (n := n) (k * R)) * tsupport a with hΩdef
  have hΩ : IsCompact Ω :=
    ((isCompact_unipBall _).image continuous_archProj).mul a.hasCompactSupport
  have key : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn a k R Ω := by
    refine hΩ.induction_on ?_ ?_ ?_ ?_
    · exact ⟨0, le_rfl, fun _ _ _ _ _ w hw => absurd hw (Set.notMem_empty w)⟩
    · rintro s t hst ⟨c, hc, h⟩
      exact ⟨c, hc, fun Y hY hR C hC w hw => h Y hY hR C hC w (hst hw)⟩
    · rintro s t ⟨c, hc, h⟩ ⟨d, hd, h'⟩
      refine ⟨max c d, le_max_of_le_left hc, fun Y hY hR C hC w hw => ?_⟩
      have hp : 0 ≤ ∏ i, ‖Y i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      rcases hw with hw | hw
      · exact (h Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
      · exact (h' Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
    · intro x _
      have hcm : Continuous fun w : G1 K n => w * x⁻¹ := continuous_id.mul continuous_const
      set V : Set (G1 K n) := (fun w : G1 K n => w * x⁻¹) ⁻¹' finUSet U hUo with hV
      have hVc : IsClopen V := (isClopen_finUSet U hUo).preimage hcm
      have hxV : x ∈ V := by
        show x * x⁻¹ ∈ finUSet U hUo
        rw [mul_inv_cancel]
        show finPart K n ((1 : G1 K n) : AdelicGLn.AdelicGL K n) ∈ (finOpenSubgroup U hUo : Set _)
        rw [Subgroup.coe_one, map_one]
        exact one_mem (finOpenSubgroup U hUo)
      refine ⟨Ω ∩ V, inter_mem_nhdsWithin _ (hVc.isOpen.mem_nhds hxV), ?_⟩
      have hTc : IsCompact ((fun w : G1 K n => infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)) '' (Ω ∩ V)) :=
        (hΩ.inter_right hVc.isClosed).image
          (continuous_infPart.comp (continuous_subtype_val.comp hcm))
      obtain ⟨c, hc, h⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local (hsm x) hTc k R
      refine ⟨c, hc, fun Y hY hR C hC w hw => ?_⟩
      have hwV : finPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) ∈
          (finOpenSubgroup U hUo : Set (AdelicGLn.FiniteAdelicGL K n)) := hw.2
      rw [coe_openSubgroupOf] at hwV
      obtain ⟨u, huU, hu⟩ := hwV
      have hg := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split hu.symm
      obtain ⟨b, hbdef⟩ : ∃ b, b = infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) := ⟨_, rfl⟩
      rw [← hbdef] at hg
      have hb := h Y hY hR C hC b ⟨w, hw, hbdef.symm⟩
      have hw' : w = finOne K n u * archP K n b * x := by
        rw [← hg, inv_mul_cancel_right]
      have hterm : ∀ ε, a ((archProj K n (C ε))⁻¹ * w) =
          a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
        intro ε
        have hpb : archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ =
            (archProj K n (C ε))⁻¹ * archP K n b := by
          rw [archimedeanProjection_apply, map_mul, map_inv, archimedeanProjection_apply]
        have e : (archProj K n (C ε))⁻¹ * w =
            finOne K n u * (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
          rw [hpb, hw', ← mul_assoc, ← mul_assoc, ← mul_assoc, archProj_inv_mul_finOne]
          simp only [mul_assoc]
        rw [e, hU u huU]
      have hs : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) =
          ∑ ε, (altSign ε : ℂ) * a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) :=
        Finset.sum_congr rfl fun ε _ => by rw [hterm ε]
      rw [hs]
      exact hb
  obtain ⟨c, hc, h⟩ := key
  refine ⟨c, fun Y hY hR C hC w => ?_⟩
  by_cases hw : w ∈ Ω
  · exact h Y hY hR C hC w hw
  · have hz : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) = 0 := by
      refine Finset.sum_eq_zero fun ε _ => ?_
      have : (archProj K n (C ε))⁻¹ * w ∉ tsupport a := fun hs =>
        hw ⟨archProj K n (C ε), ⟨C ε, mem_unipBall_of_val_eq hY hR (hC ε), rfl⟩, _, hs, mul_inv_cancel_left _ _⟩
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
    rw [hz, norm_zero]
    exact mul_nonneg hc (Finset.prod_nonneg fun i _ => norm_nonneg _)
end

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

open scoped Pointwise

private theorem sub_ct_le_of_altSum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n) (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne (K := _) (n := _) r s * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => rc μ f φ (unipOne (K := _) (n := _) r s * x) with hH
  set c : ℂ := ct r (rc μ f φ) x with hc
  have hHc : Continuous H :=
    (continuous_rconv (Gam K n) μ f φ).comp ((continuous_unipOne r).mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := by
    intro ξ hξ s
    simp only [H, rc]
    rw [unipOne_add, mul_assoc,
      rconv_mul_left (Gam K n) μ f φ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hcint : IntegrableOn (fun _ : UPos n r → 𝔸[K] => c) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    integrableOn_const (by rw [hD1]; exact ENNReal.one_ne_top)
  have hmean0 : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = c := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    rfl
  have hi0 : IntegrableOn H (scaledUnipFD K n r M) (unipMeasure K n r) := by simpa using hint 0
  have hmean : ∫ y in scaledUnipFD K n r M, (H y - c) ∂unipMeasure K n r = 0 := by
    rw [integral_sub hi0 hcint, hmean0, setIntegral_const, measureReal_def, hD1]
    simp
  have h0 := norm_le_of_forall_altSum_le hD hD1 (k + 1) (fun s => H s - c)
    (fun ξ hξ s => by simp only [hper ξ hξ s]) (fun t => (hint t).sub hcint) hmean B (fun y hy => by
      have := hB y hy
      rw [altSum_succ] at this ⊢
      simpa only [sub_sub_sub_cancel_right] using this)
  simpa [H, unipOne_zero] using h0

private theorem sub_ct_le_of_altSum_inf {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n)
    (hfin : ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
      (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
        (z p).2 = (M : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * a) →
      ∀ w, f ((x⁻¹ * unipOne (K := _) (n := _) r z * x)⁻¹ * w) = f w)
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne (K := _) (n := _) r (truncInf s) * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  refine sub_ct_le_of_altSum (r := r) μ f φ hM x k fun y hy => ?_
  have key : ∀ ε : Fin (k + 1) → Bool,
      rc μ f φ (unipOne (K := _) (n := _) r (0 + altPoint y ε) * x) =
        rc μ f φ (unipOne (K := _) (n := _) r (truncInf (0 + altPoint y ε)) * x) := by
    intro ε
    rw [zero_add]
    have hfinP := hfin (truncFin (altPoint y ε)) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    have hP : unipOne (K := _) (n := _) r (altPoint y ε) * x = unipOne (K := _) (n := _) r (truncInf (altPoint y ε)) * x *
        (x⁻¹ * unipOne (K := _) (n := _) r (truncFin (altPoint y ε)) * x) := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← unipOne_add, truncInf_add_truncFin]
    rw [hP]
    exact rconv_mul_right μ f φ hfinP _
  have heq : altSum (k + 1) (fun s => rc μ f φ (unipOne (K := _) (n := _) r s * x)) y 0 =
      altSum (k + 1) (fun s => rc μ f φ (unipOne (K := _) (n := _) r (truncInf s) * x)) y 0 := by
    rw [altSum_eq_sum, altSum_eq_sum]
    exact Finset.sum_congr rfl fun ε _ => congrArg (altSign ε • ·) (key ε)
  rw [heq]
  exact hB y hy

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.rootDecay :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n), IsLeftSmooth a → ∀ (ω : Set (AdelicGLn.AdelicGL K n)) (t : ℝ), Bor ω → 0 < t →
      ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ (φ : L2 μ) (ρ : Fin n → ℝ) (x : G1 K n) (R : ℝ), Sg ω ρ x → Full t ρ → 1 ≤ R → Rat R ρ →
        ‖rc μ a φ x - ct r (rc μ a φ) x‖ ≤ C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * R ^ N * ‖φ‖ := by
  intro K _ _ n μ _ f hf ω t hBor ht r hr hrn
  obtain ⟨hω, hωB⟩ := hBor
  obtain ⟨U, hU, hUf⟩ := hf.2
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : normOneGL (K := K) (n := n))
  obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht hV₀c
  refine ⟨N, fun k => ?_⟩
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  set R₁ := C₁' * t⁻¹
  obtain ⟨c, hc⟩ := diffBd f hf (k + 1) R₁
  set c' := max c 0
  have h𝒞 := isCompact_unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁)
  set Q := archProj K n '' unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) *
    tsupport (f : normOneGL (K := K) (n := n) → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  obtain ⟨s, -, hs⟩ := hQ.elim_nhds_subcover (fun g => (fun y => y * g) '' V₀) fun g _ => by
    have := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hV₀
    rw [Homeomorph.coe_mulRight] at this
    simpa only [one_mul] using this
  refine ⟨c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)), ?_⟩
  rintro φ ρ x R ⟨hρ, b, hb, kk, hkk, hx⟩ hsieg hR1 hR
  obtain ⟨m₀, hmC₀, hm₀⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = s.card * m₀ := ⟨_, rfl⟩
  have hm : ∀ z : normOneGL (K := K) (n := n),
      {γ : rationalGLOne (K := K) (n := n) | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
    intro z
    have := encard_le_of_subset_mul s hs hm₀ z
    rw [hmdef]
    exact_mod_cast this
  have hmC : (m : ℝ) ≤ s.card * Cc * R ^ N := by
    rw [hmdef, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC₀ (Nat.cast_nonneg _)
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  have hgR : C₁' * gain ≤ R₁ := mul_le_mul_of_nonneg_left hgain hC₁'0
  have hg0 : 0 ≤ C₁' * gain := mul_nonneg hC₁'0 hgain0
  set b₀ := c' * ((C₁' * gain) ^ k * R₁)
  have hb₀ : 0 ≤ b₀ := mul_nonneg hc'0 (mul_nonneg (pow_nonneg hg0 _) (hg0.trans hgR))
  have hfinal : ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ b₀ * √(μ.real Q * m) * ‖φ‖ := by
    refine sub_ct_le_of_altSum_inf (r := r) μ f φ hM x ?_ k ?_
    · intro z hz1 hz2 w
      obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk z hz1 hz2
      have hxu : x⁻¹ * unipOne (K := _) (n := _) r z * x = finOne K n (u : AdelicGLn.integralFiniteGL K n) := by
        refine Subtype.ext ?_
        change (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL z * (x : AdelicGLn.AdelicGL K n) =
          finEmb K n _
        rw [hx]
        exact hu
      rw [hxu, ← map_inv]
      exact hUf _ (U.inv_mem u.2) w
    · intro y hy
      set Y : Fin (k + 1) → ArchMatrix K n :=
        fun i => conjArch K n (x : AdelicGLn.AdelicGL K n) (truncInf (y i))
      have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
      have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
        intro i
        have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
          (fun p => infinite_mem_scaledInfSet hM (hy i) p)
        have h2 : Y i = archMat K n ((((b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) *
            kk)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            blockEntry (truncInf (y i)) * ((b * diagUnits n (fun i => posIdele (K := K) (ρ i)
              (hρ i)) * kk : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
          simp only [Y, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
        rw [h2]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
      have hYR : ∀ i, ‖Y i‖ ≤ R₁ := fun i => (hYn i).trans hgR
      have hex : ∀ ε : Fin (k + 1) → Bool, ∃ C : ArchUnits K n,
          archProj K n C = x⁻¹ * unipOne (K := _) (n := _) r (truncInf (altPoint y ε)) * x ∧
            (C : ArchMatrix K n) = 1 + altPoint Y ε := by
        intro ε
        obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq_conj x (truncInf (altPoint y ε)) fun p => rfl
        refine ⟨C, hC1, ?_⟩
        rw [hC2, ← truncInfHom_apply, map_altPoint (truncInfHom n r),
          map_altPoint (conjArch K n (x : AdelicGLn.AdelicGL K n))]
        rfl
      choose Cε hCε1 hCε2 using hex
      have hsum : altSum (k + 1) (fun s => rc μ f φ (unipOne (K := _) (n := _) r (truncInf s) * x)) y 0 =
          ∑ ε, (altSign ε : ℂ) * rconv (rationalGLOne (K := K) (n := n)) μ f φ (x * archProj K n (Cε ε)) := by
        rw [altSum_eq_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [zero_add, hCε1 ε, zsmul_eq_mul]
        have : x * (x⁻¹ * unipOne (K := _) (n := _) r (truncInf (altPoint y ε)) * x) =
            unipOne (K := _) (n := _) r (truncInf (altPoint y ε)) * x := by group
        rw [this]
      rw [hsum]
      have hb' : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (Cε ε))⁻¹ * w)‖ ≤ b₀ := by
        intro w
        refine (hc Y hYY hYR Cε hCε2 w).trans ?_
        have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ (k + 1) := by
          rw [← Fin.prod_const]
          exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hYn i
        have hprod' : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k * R₁ := by
          refine hprod.trans ?_
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hgR (pow_nonneg hg0 _)
        calc c * ∏ i, ‖Y i‖ ≤ c' * ∏ i, ‖Y i‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ b₀ := mul_le_mul_of_nonneg_left hprod' hc'0
      have hmem : ∀ ε, Cε ε ∈ unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) := fun ε =>
        mem_unipBall_of_val_eq hYY hYR (hCε2 ε)
      let ccTranslate (g : normOneGL (K := K) (n := n)) (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) :
          CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ :=
        ⟨⟨fun w => f (g⁻¹ * w), f.continuous.comp (continuous_const_mul _)⟩,
          f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩
      
      have rconv_mul_eq (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ)
          (φ : Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) (x g : normOneGL (K := K) (n := n)) :
          rconv (rationalGLOne (K := K) (n := n)) μ f φ (x * g) = rconv (rationalGLOne (K := K) (n := n)) μ (ccTranslate g f) φ x := by
        unfold rconv
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        change f ((x * g)⁻¹ * z) * _ = f (g⁻¹ * (x⁻¹ * z)) * _
        rw [mul_inv_rev, mul_assoc]
      
      have sum_altSign_rconv_eq (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ)
          (φ : Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) (x : normOneGL (K := K) (n := n)) {k : ℕ}
          (C : (Fin k → Bool) → ArchUnits K n) :
          ∑ ε, (altSign ε : ℂ) * rconv (rationalGLOne (K := K) (n := n)) μ f φ (x * archProj K n (C ε)) =
            rconv (rationalGLOne (K := K) (n := n)) μ (fun w => ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w)) φ x := by
        simp_rw [rconv_mul_eq f φ x]
        unfold rconv
        simp_rw [← integral_const_mul]
        rw [← integral_finsetSum _ fun ε _ => (integrable_rconv (rationalGLOne (K := K) (n := n)) μ _ φ x).const_mul _]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ε _ => ?_
        simp only [ccTranslate]
        change _ * (f ((archProj K n (C ε))⁻¹ * (x⁻¹ * z)) * _) = _
        ring
      set_option synthInstance.maxHeartbeats 200000 in
      have enorm_sum_altSign_rconv_sq_le (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ)
          (φ : Lp ℂ 2 (quotientMeasure (rationalGLOne (K := K) (n := n)) μ)) (x : normOneGL (K := K) (n := n)) {k : ℕ} {𝒞 : Set (ArchUnits K n)}
          (h𝒞 : IsCompact 𝒞) (C : (Fin k → Bool) → ArchUnits K n) (hC : ∀ ε, C ε ∈ 𝒞) {b : ℝ}
          (hb : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w)‖ ≤ b) {m : ℕ}
          (hm : ∀ z : normOneGL (K := K) (n := n), {γ : (rationalGLOne (K := K) (n := n)) | γ • z ∈ (fun y => x * y) ''
            (archProj K n '' 𝒞 * tsupport (f : normOneGL (K := K) (n := n) → ℂ))}.encard ≤ m) :
          ‖∑ ε, (altSign ε : ℂ) * rconv (rationalGLOne (K := K) (n := n)) μ f φ (x * archProj K n (C ε))‖ₑ ^ 2 ≤
            ENNReal.ofReal b ^ 2 * μ (archProj K n '' 𝒞 * tsupport (f : normOneGL (K := K) (n := n) → ℂ)) *
              (m * ‖φ‖ₑ ^ 2) := by
        set Q := archProj K n '' 𝒞 * tsupport (f : normOneGL (K := K) (n := n) → ℂ)
        have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
        have hsupp : ∀ w ∉ Q, ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w) = 0 := by
          intro w hw
          refine Finset.sum_eq_zero fun ε _ => ?_
          have : (archProj K n (C ε))⁻¹ * w ∉ tsupport (f : normOneGL (K := K) (n := n) → ℂ) := fun h' =>
            hw ⟨archProj K n (C ε), ⟨C ε, hC ε, rfl⟩, _, h', mul_inv_cancel_left _ _⟩
          rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
        set Ψ : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ :=
          ⟨⟨fun w => ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w),
            continuous_finsetSum _ fun ε _ => continuous_const.mul
              (f.continuous.comp (continuous_const_mul _))⟩, HasCompactSupport.intro hQ hsupp⟩
        rw [sum_altSign_rconv_eq f φ x C]
        have hS : MeasurableSet ((fun y => x * y) '' Q) := (hQ.image (continuous_const_mul x)).measurableSet
        have h1 := enorm_rconv_sq_le (rationalGLOne (K := K) (n := n)) μ Ψ φ x hS (fun y hy => hsupp _ fun hq => hy ⟨_, hq, by simp⟩) hm
        refine h1.trans ?_
        gcongr
        calc ∫⁻ y, ‖Ψ y‖ₑ ^ 2 ∂μ = ∫⁻ y in Q, ‖Ψ y‖ₑ ^ 2 ∂μ := by
              rw [← lintegral_indicator hQ.measurableSet]
              refine lintegral_congr fun y => ?_
              by_cases hy : y ∈ Q
              · rw [indicator_of_mem hy]
              · rw [indicator_of_notMem hy]
                change ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * y)‖ₑ ^ 2 = 0
                rw [hsupp y hy]
                simp
          _ ≤ ∫⁻ _ in Q, ENNReal.ofReal b ^ 2 ∂μ := by
              refine setLIntegral_mono' hQ.measurableSet fun y _ => ?_
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hb y)
          _ = ENNReal.ofReal b ^ 2 * μ Q := by rw [setLIntegral_const]
      have hsq := enorm_sum_altSign_rconv_sq_le f φ x h𝒞 Cε hmem hb' hm
      have hA : ENNReal.ofReal b₀ ^ 2 * μ Q * (m : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hQ.measure_lt_top.ne) (by simp)
      have hle := norm_le_of_enorm_sq_le hA (by rw [mul_assoc]; exact hsq)
      refine hle.trans (le_of_eq ?_)
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb₀,
        ENNReal.toReal_natCast, Real.sqrt_mul (by positivity), Real.sqrt_mul' _ (by positivity),
        Real.sqrt_sq hb₀, measureReal_def, mul_assoc, Real.sqrt_mul ENNReal.toReal_nonneg]
  refine hfinal.trans ?_
  have hμQ : 0 ≤ μ.real Q := measureReal_nonneg
  have hRN : 1 ≤ R ^ N := one_le_pow₀ hR1
  have hm' : (m : ℝ) ≤ s.card * max Cc 0 * R ^ N :=
    hmC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (Nat.cast_nonneg _)) (pow_nonneg (by linarith) _))
  have hsqrt : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * √(R ^ N) := by
    rw [← Real.sqrt_mul (mul_nonneg hμQ (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm' hμQ
  have hsR : √(R ^ N) ≤ R ^ N := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsqrt' : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * R ^ N :=
    hsqrt.trans (mul_le_mul_of_nonneg_left hsR (Real.sqrt_nonneg _))
  calc b₀ * √(μ.real Q * m) * ‖φ‖
      ≤ b₀ * (√(μ.real Q * (s.card * max Cc 0)) * R ^ N) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt' hb₀) (norm_nonneg _)
    _ = c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)) * gain ^ k * R ^ N * ‖φ‖ := by
        simp only [b₀, mul_pow]
        ring
end

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem pow_arith (c : ℝ) (hc : 0 < c) (A B : ℕ) :
    ∃ k : ℕ, ∀ y u : ℝ, 1 ≤ y → 0 ≤ u → u ≤ (y ^ c)⁻¹ → u ^ k * y ^ A ≤ (y ^ B)⁻¹ := by
  obtain ⟨k, hk⟩ := exists_nat_ge (((A : ℝ) + B) / c)
  refine ⟨k, fun y u hy hu huy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hk' : (A : ℝ) + B ≤ c * k := by
    rw [div_le_iff₀ hc] at hk
    linarith
  have h1 : u ^ k ≤ ((y ^ c)⁻¹) ^ k := pow_le_pow_left₀ hu huy k
  have h2 : ((y ^ c)⁻¹) ^ k = (y ^ (c * k))⁻¹ := by
    rw [inv_pow, ← Real.rpow_natCast (y ^ c), ← Real.rpow_mul hy0.le]
  have h3 : y ^ ((A : ℝ) + B) ≤ y ^ (c * k) := Real.rpow_le_rpow_of_exponent_le hy hk'
  have h4 : y ^ ((A : ℝ) + B) = y ^ A * y ^ B := by
    rw [Real.rpow_add hy0, Real.rpow_natCast, Real.rpow_natCast]
  have hyA : 0 < y ^ A := pow_pos hy0 A
  have hyB : 0 < y ^ B := pow_pos hy0 B
  have h5 : (y ^ (c * k))⁻¹ ≤ (y ^ A * y ^ B)⁻¹ := by
    rw [← h4]
    exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _) h3
  calc u ^ k * y ^ A ≤ (y ^ A * y ^ B)⁻¹ * y ^ A :=
        mul_le_mul_of_nonneg_right ((h2 ▸ h1).trans h5) hyA.le
    _ = (y ^ B)⁻¹ := by field_simp

private theorem pow_arith2 (c : ℝ) (hc : 0 < c) (N N' : ℕ) :
    ∃ k : ℕ, ∀ y R u : ℝ, 1 ≤ y → 1 ≤ R → y ^ c ≤ R → 0 ≤ u → u ≤ (R ^ c)⁻¹ →
      u ^ k * R ^ N ≤ (y ^ N')⁻¹ := by
  obtain ⟨B, hB⟩ := exists_nat_ge ((N' : ℝ) / c)
  obtain ⟨k, hk⟩ := pow_arith c hc N B
  refine ⟨k, fun y R u hy hR hyR hu huR => (hk R u hR hu huR).trans ?_⟩
  have hy0 : 0 < y := by linarith
  have hB' : (N' : ℝ) ≤ c * B := by
    rw [div_le_iff₀ hc] at hB
    linarith
  have h1 : y ^ N' ≤ (y ^ c) ^ B := by
    rw [← Real.rpow_natCast y N', ← Real.rpow_natCast (y ^ c) B, ← Real.rpow_mul hy0.le]
    exact Real.rpow_le_rpow_of_exponent_le hy hB'
  have h2 : (y ^ c) ^ B ≤ R ^ B := pow_le_pow_left₀ (Real.rpow_nonneg hy0.le _) hyR B
  exact inv_anti₀ (pow_pos hy0 _) (h1.trans h2)

section

variable {K : Type} [Field K] [NumberField K]

private theorem sec_norm_le {d : ℕ} (sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)) (U : ℝ → Eu d) (B : ℝ)
    (hU : ∀ s, ‖U s‖ ≤ B) (z : G1 K (2 + 2)) :
    ‖secF sec U z‖ ≤ B * ∑ i, Real.exp (2 * HH z) * ‖sec (EuclideanSpace.basisFun (Fin d) ℂ i) z‖ := by
  set b := EuclideanSpace.basisFun (Fin d) ℂ with hb
  set v := U (HH z) with hv
  have hsum : sec v z = ∑ i, b.repr v i * sec (b i) z := by
    conv_lhs => rw [← b.sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.sum_apply]
  have hc : ∀ i, ‖b.repr v i‖ ≤ B := fun i =>
    (PiLp.norm_apply_le (b.repr v) i).trans ((b.repr.norm_map v).le.trans (hU _))
  have hexp : ‖Complex.exp (2 * (HH z : ℂ))‖ = Real.exp (2 * HH z) := by
    rw [Complex.norm_exp]
    simp
  unfold secF
  rw [norm_mul, hexp, hsum]
  have h : ‖∑ i, b.repr v i * sec (b i) z‖ ≤ ∑ i, B * ‖sec (b i) z‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))
  calc Real.exp (2 * HH z) * ‖∑ i, b.repr v i * sec (b i) z‖
      ≤ Real.exp (2 * HH z) * ∑ i, B * ‖sec (b i) z‖ :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = B * ∑ i, Real.exp (2 * HH z) * ‖sec (b i) z‖ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

private theorem far_fam {ι : Type} [Fintype ι] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ) (hR : Red ω t)
    (f : ι → G1 K (2 + 2) → ℂ) (hf : ∀ i, SFun (f i)) :
    (∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x)) →
        ∑ q ∈ S, ∑ i, Real.exp (2 * HH (qx q x)) * ‖f i (qx q x)‖ ≤ C * qht x ^ N) ∧
      ∀ (ε : ℝ) (N' : ℕ), 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
        (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
        ∑ q ∈ S, ∑ i, Real.exp (2 * HH (qx q x)) * ‖f i (qx q x)‖ ≤ C * (qht x ^ N')⁻¹ := by
  have hq1 : ∀ x : G1 K (2 + 2), 1 ≤ qht x := (qhtBasic K (2 + 2)).1
  constructor
  · choose C N hC using fun i => (farSum ω t hR (f i) (hf i)).1
    refine ⟨∑ i, |C i|, ∑ i, N i, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x S hS => ?_⟩
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (hC i x S hS).trans ?_
    have h0 : (0 : ℝ) < qht x ^ N i := pow_pos (by linarith [hq1 x]) _
    have h1 : qht x ^ N i ≤ qht x ^ ∑ i, N i :=
      pow_le_pow_right₀ (hq1 x) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) h0.le).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
  · intro ε N' hε
    choose C hC using fun i => (farSum ω t hR (f i) (hf i)).2 ε N' hε
    refine ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x S hS => ?_⟩
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (hC i x S hS).trans ?_
    have h0 : (0 : ℝ) ≤ (qht x ^ N')⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith [hq1 x]) _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) h0

private theorem th_hi_eq (T : ℝ) (F : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) :
    ∃ S : Finset (Cos K), (∀ q, q ∈ S ↔ T < HH (qx q x)) ∧ th (hi T F) x = ∑ q ∈ S, F (qx q x) := by
  have hfin : {q : Cos K | T < HH (qx q x)}.Finite :=
    (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, le_of_lt hq⟩
  refine ⟨hfin.toFinset, fun q => by simp, ?_⟩
  unfold th
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have : T < HH (qx q x) := by simpa using hq
    exact Set.indicator_of_mem (s := {z : G1 K (2 + 2) | T < HH z}) this F
  · intro q hq
    by_contra hn
    have hn' : ¬ T < HH (qx q x) := by simpa using hn
    exact hq (Set.indicator_of_notMem (s := {z : G1 K (2 + 2) | T < HH z}) hn' F)

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.mainBd :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → IsLeftSmooth a → D.Hecke a → ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (x : G1 K (2 + 2)) (φ : L2 μ), 0 ≤ T → P φ = φ → ¬ Om T x → ‖lam T (rc μ a φ) x‖ ≤ C * (qht x ^ N')⁻¹ * ‖φ‖ := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP ha hD N'
  classical
  obtain ⟨ω, t, hR⟩ := redEx (K := K)
  have hq1 : ∀ x : G1 K (2 + 2), 1 ≤ qht x := (qhtBasic K (2 + 2)).1
  have hfA : ∀ i, SFun (A.sec (EuclideanSpace.basisFun (Fin d) ℂ i)) := fun i => by
    have h := (A.onto (A.sec (EuclideanSpace.basisFun (Fin d) ℂ i))).1 ⟨_, rfl⟩
    exact secFun μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ h.1 h.2
  have hfB : ∀ i, SFun (A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i)) := fun i => by
    have h := (A'.onto (A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i))).1 ⟨_, rfl⟩
    exact secFun μ₂ τ₂ τ₁ D hp.irr₂ hp.irr₁ _ h.1 h.2
  obtain ⟨⟨Ca, Na, hCa, hNa⟩, hFarA⟩ := far_fam ω t hR _ hfA
  obtain ⟨⟨Cb, Nb, hCb, hNb⟩, hFarB⟩ := far_fam ω t hR _ hfB
  obtain ⟨C₀, hC₀⟩ := ctRep K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP hD

  set G : G1 K (2 + 2) → ℝ := fun z =>
    (∑ i, Real.exp (2 * HH z) * ‖A.sec (EuclideanSpace.basisFun (Fin d) ℂ i) z‖) +
      ∑ i, Real.exp (2 * HH z) * ‖A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i) z‖ with hG
  have hct : ∀ φ, P φ = φ → ∀ z, ‖ct 2 (rc μ a φ) z‖ ≤ |C₀| * ‖φ‖ * G z := by
    intro φ hφ z
    obtain ⟨U, U', -, -, hU, -, -, hrep⟩ := hC₀ φ hφ
    have hB : ∀ s, ‖U s‖ ≤ |C₀| * ‖φ‖ ∧ ‖U' s‖ ≤ |C₀| * ‖φ‖ := fun s =>
      ⟨(hU s).1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)),
        (hU s).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))⟩
    rw [hrep z, hG]
    simp only [mul_add]
    exact (norm_add_le _ _).trans (add_le_add (sec_norm_le _ U _ (fun s => (hB s).1) z)
      (sec_norm_le _ U' _ (fun s => (hB s).2) z))
  have hsum : ∀ φ, P φ = φ → ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
      ‖∑ q ∈ S, ct 2 (rc μ a φ) (qx q x)‖ ≤ |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) := by
    intro φ hφ x S
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hct φ hφ _)
  obtain ⟨ε, c, Q, M, hε, hc, hgeo⟩ := geo ω t hR
  obtain ⟨CA, hCA, hA⟩ := hFarA ε N' hε
  obtain ⟨CB, hCB, hB⟩ := hFarB ε N' hε
  obtain ⟨Cp, Np, hpoly⟩ := polyBdAll K (2 + 2) μ a
  obtain ⟨N₂, h₂⟩ := rootDecay μ a ha ω t hR.bor hR.pos 2 (by norm_num) (by norm_num)
  obtain ⟨N₁, h₁⟩ := rootDecay μ a ha ω t hR.bor hR.pos 1 (by norm_num) (by norm_num)
  obtain ⟨N₃, h₃⟩ := rootDecay μ a ha ω t hR.bor hR.pos 3 (by norm_num) (by norm_num)
  obtain ⟨k₂, hk₂⟩ := pow_arith c hc (M * N₂) N'
  obtain ⟨k₁, hk₁⟩ := pow_arith2 c hc N₁ N'
  obtain ⟨k₃, hk₃⟩ := pow_arith2 c hc N₃ N'
  obtain ⟨D₂, hD₂⟩ := h₂ k₂
  obtain ⟨D₁, hD₁⟩ := h₁ k₁
  obtain ⟨D₃, hD₃⟩ := h₃ k₃
  have hvan := (ctVanish K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP).1

  set E : ℝ := |C₀| * (CA + CB) with hE
  have hE0 : 0 ≤ E := mul_nonneg (abs_nonneg _) (add_nonneg hCA hCB)
  have hfar : ∀ φ, P φ = φ → ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
      (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
      ‖∑ q ∈ S, ct 2 (rc μ a φ) (qx q x)‖ ≤ E * (qht x ^ N')⁻¹ * ‖φ‖ := by
    intro φ hφ x S hS
    refine (hsum φ hφ x S).trans ?_
    have h : ∑ q ∈ S, G (qx q x) ≤ (CA + CB) * (qht x ^ N')⁻¹ := by
      rw [hG]
      simp only [Finset.sum_add_distrib, add_mul]
      exact add_le_add (hA x S hS) (hB x S hS)
    calc |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) ≤ |C₀| * ‖φ‖ * ((CA + CB) * (qht x ^ N')⁻¹) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = E * (qht x ^ N')⁻¹ * ‖φ‖ := by rw [hE]; ring

  set Q' : ℝ := max Q 1 with hQ'
  have hQ1 : 1 ≤ Q' := le_max_right _ _
  set Cs : ℝ := (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * Q' ^ N' with hCs
  have hCs0 : 0 ≤ Cs := by
    have : (0 : ℝ) ≤ Q' := by linarith
    positivity
  refine ⟨Cs + (|D₁| + |D₂| + |D₃|) + E, by positivity, fun T x φ hT hφ hOm => ?_⟩
  set y := qht x with hy
  have hy1 : 1 ≤ y := hq1 x
  have hy0 : 0 < y := by linarith
  have hyi : 0 < (y ^ N')⁻¹ := inv_pos.2 (pow_pos hy0 _)
  have hn0 : 0 ≤ ‖φ‖ := norm_nonneg _
  set ψ := rc μ a φ with hψ
  obtain ⟨S, hS, hth⟩ := th_hi_eq T (ct 2 ψ) x
  obtain ⟨-, -, hGam₀, hPK₀, -⟩ := (ctKv μ a).2 φ
  have hGam : ∀ γ ∈ Gam K (2 + 2), ∀ x, ψ (γ * x) = ψ x := hGam₀
  have hPK : ∀ γ ∈ PK K, ∀ z, ct 2 ψ (γ * z) = ct 2 ψ z := hPK₀
  have hlam : lam T ψ x = ψ x - ∑ q ∈ S, ct 2 ψ (qx q x) := by
    rw [lam, hth]
  rw [hlam]
  have hHH : ∀ q ∈ S, 0 ≤ HH (qx q x) := fun q hq => hT.trans ((hS q).1 hq).le
  by_cases hQ : y < Q
  ·
    have hyQ : y ≤ Q' := hQ.le.trans (le_max_left _ _)
    have hpw : ∀ n : ℕ, y ^ n ≤ Q' ^ n := fun n => pow_le_pow_left₀ hy0.le hyQ n
    have h1 : ‖ψ x‖ ≤ |Cp| * Q' ^ Np * ‖φ‖ := by
      refine (hpoly φ x).trans (mul_le_mul_of_nonneg_right ?_ hn0)
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos hy0 _).le).trans
        (mul_le_mul_of_nonneg_left (hpw _) (abs_nonneg _))
    have h2 : ‖∑ q ∈ S, ct 2 ψ (qx q x)‖ ≤ |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb) * ‖φ‖ := by
      refine (hsum φ hφ x S).trans ?_
      have h : ∑ q ∈ S, G (qx q x) ≤ Ca * Q' ^ Na + Cb * Q' ^ Nb := by
        rw [hG]
        simp only [Finset.sum_add_distrib]
        exact add_le_add ((hNa x S hHH).trans (mul_le_mul_of_nonneg_left (hpw _) hCa))
          ((hNb x S hHH).trans (mul_le_mul_of_nonneg_left (hpw _) hCb))
      calc |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) ≤ |C₀| * ‖φ‖ * (Ca * Q' ^ Na + Cb * Q' ^ Nb) :=
            mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) hn0)
        _ = _ := by ring
    have h3 : 1 ≤ Q' ^ N' * (y ^ N')⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (pow_pos hy0 _)]
      exact hpw _
    have hB0 : 0 ≤ |Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb) := by
      have : (0 : ℝ) ≤ Q' := by linarith
      positivity
    calc ‖ψ x - ∑ q ∈ S, ct 2 ψ (qx q x)‖
        ≤ (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * ‖φ‖ := by
          rw [add_mul]
          exact (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ ≤ (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * (Q' ^ N' * (y ^ N')⁻¹) * ‖φ‖ :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hB0 h3) hn0
      _ = Cs * (y ^ N')⁻¹ * ‖φ‖ := by rw [hCs]; ring
      _ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hyi.le) hn0
          have := abs_nonneg D₁
          have := abs_nonneg D₂
          have := abs_nonneg D₃
          linarith
  · have hQy : Q ≤ y := not_lt.1 hQ

    have fin : ∀ (Dc : ℝ) (w : ℂ) (S' : Finset (Cos K)), |Dc| ≤ |D₁| + |D₂| + |D₃| →
        ‖w‖ ≤ |Dc| * (y ^ N')⁻¹ * ‖φ‖ → ‖∑ q ∈ S', ct 2 ψ (qx q x)‖ ≤ E * (y ^ N')⁻¹ * ‖φ‖ →
        ‖w‖ + ‖∑ q ∈ S', ct 2 ψ (qx q x)‖ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ := by
      intro Dc w S' hDc h1 h2
      have h3 : (|Dc| + E) * (y ^ N')⁻¹ * ‖φ‖ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hyi.le) hn0
      have h4 : (|Dc| + E) * (y ^ N')⁻¹ * ‖φ‖ = |Dc| * (y ^ N')⁻¹ * ‖φ‖ + E * (y ^ N')⁻¹ * ‖φ‖ := by ring
      linarith
    have scale : ∀ Dc v : ℝ, 0 ≤ v → v ≤ (y ^ N')⁻¹ → Dc * v * ‖φ‖ ≤ |Dc| * (y ^ N')⁻¹ * ‖φ‖ := by
      intro Dc v hv0 hv
      refine mul_le_mul_of_nonneg_right ?_ hn0
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) hv0).trans
        (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
    have hd1 : |D₁| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₂
      have := abs_nonneg D₃
      linarith
    have hd2 : |D₂| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₁
      have := abs_nonneg D₃
      linarith
    have hd3 : |D₃| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₁
      have := abs_nonneg D₂
      linarith
    rcases hgeo T x hT hQy hOm with ⟨q₀, δ, hδ, ρ, hSg, hFull, hTq, hratio, hRat, hoth⟩ | ⟨γ, hγ, ρ, R, hSg, hFull, hR1, hRat, hyR, hcase, hoth⟩
    ·
      obtain ⟨hρ, -⟩ := id hSg
      have hq₀ : q₀ ∈ S := (hS q₀).2 hTq
      rw [← Finset.add_sum_erase S _ hq₀]
      have hδG : δ ∈ Gam K (2 + 2) := by
        obtain ⟨p, -, rfl⟩ := hδ
        exact p.2
      have e1 : ψ x = ψ (δ * qx q₀ x) := by
        rw [hGam δ hδG, hGam _ q₀.out.2]
      have e2 : ct 2 ψ (qx q₀ x) = ct 2 ψ (δ * qx q₀ x) := (hPK δ hδ _).symm
      have hb : ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ ≤
          D₂ * (ρ 2 / ρ 1) ^ k₂ * (y ^ M) ^ N₂ * ‖φ‖ :=
        hD₂ φ ρ _ (y ^ M) hSg hFull (one_le_pow₀ hy1) hRat
      have hu0 : 0 ≤ ρ 2 / ρ 1 := (div_pos (hρ 2) (hρ 1)).le
      have hu : ρ 2 / ρ 1 ≤ (y ^ c)⁻¹ := by
        rw [← inv_div (ρ 1) (ρ 2)]
        exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _) hratio
      have hv := hk₂ y _ hy1 hu0 hu
      rw [pow_mul y M N₂] at hv
      have hb' : ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ ≤ |D₂| * (y ^ N')⁻¹ * ‖φ‖ := by
        refine hb.trans ?_
        rw [mul_assoc D₂]
        exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_pos (pow_pos hy0 _) _).le) hv
      have hd : ‖ψ x - (ct 2 ψ (qx q₀ x) + ∑ q ∈ S.erase q₀, ct 2 ψ (qx q x))‖ ≤
          ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ + ‖∑ q ∈ S.erase q₀, ct 2 ψ (qx q x)‖ := by
        rw [e2, ← sub_sub, ← e1]
        exact norm_sub_le _ _
      exact hd.trans (fin D₂ _ _ hd2 hb' (hfar φ hφ x _ fun q hq =>
        ⟨hHH q (Finset.mem_of_mem_erase hq),
          hoth q (Finset.ne_of_mem_erase hq) ((hS q).1 (Finset.mem_of_mem_erase hq))⟩))
    ·
      obtain ⟨hρ, -⟩ := id hSg
      have e1 : ψ x = ψ (γ * x) := (hGam γ hγ x).symm
      have htail := hfar φ hφ x S fun q hq => ⟨hHH q hq, hoth q ((hS q).1 hq)⟩
      rw [e1]
      rcases hcase with hc1 | hc3
      · have hb : ‖ψ (γ * x) - ct 1 ψ (γ * x)‖ ≤ D₁ * (ρ 1 / ρ 0) ^ k₁ * R ^ N₁ * ‖φ‖ :=
          hD₁ φ ρ _ R hSg hFull hR1 hRat
        rw [(hvan φ hφ _).1, sub_zero] at hb
        have hu0 : 0 ≤ ρ 1 / ρ 0 := (div_pos (hρ 1) (hρ 0)).le
        have hu : ρ 1 / ρ 0 ≤ (R ^ c)⁻¹ := by
          rw [← inv_div (ρ 0) (ρ 1)]
          exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hc1
        have hv := hk₁ y R _ hy1 hR1 hyR hu0 hu
        have hb' : ‖ψ (γ * x)‖ ≤ |D₁| * (y ^ N')⁻¹ * ‖φ‖ := by
          refine hb.trans ?_
          rw [mul_assoc D₁]
          exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _)) hv
        exact (norm_sub_le _ _).trans (fin D₁ _ _ hd1 hb' htail)
      · have hb : ‖ψ (γ * x) - ct 3 ψ (γ * x)‖ ≤ D₃ * (ρ 3 / ρ 2) ^ k₃ * R ^ N₃ * ‖φ‖ :=
          hD₃ φ ρ _ R hSg hFull hR1 hRat
        rw [(hvan φ hφ _).2, sub_zero] at hb
        have hu0 : 0 ≤ ρ 3 / ρ 2 := (div_pos (hρ 3) (hρ 2)).le
        have hu : ρ 3 / ρ 2 ≤ (R ^ c)⁻¹ := by
          rw [← inv_div (ρ 2) (ρ 3)]
          exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hc3
        have hv := hk₃ y R _ hy1 hR1 hyR hu0 hu
        have hb' : ‖ψ (γ * x)‖ ≤ |D₃| * (y ^ N')⁻¹ * ‖φ‖ := by
          refine hb.trans ?_
          rw [mul_assoc D₃]
          exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _)) hv
        exact (norm_sub_le _ _).trans (fin D₃ _ _ hd3 hb' htail)
