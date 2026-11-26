module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqSiegelParabolicOperatorEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqSiegelParabolicOperatorEq
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem parFun_lintegral_sq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ _ hψ1 _ χ _ hres _ _ μ _ p hp φ
  obtain ⟨h1, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  obtain ⟨-, htop, -, -, -, -, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨-, -, -, hnorm, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have h1' := mul_eq_one_comm.mp h1
  let A : GL ν E := ⟨(mat c p).toBlocks₁₁, _, h1, h1'⟩
  have hA : ((A : GL ν E) : Matrix ν ν E) = (mat c p).toBlocks₁₁ := rfl
  set D : NNReal := distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) with hD
  have hD0 : D ≠ 0 := distribHaarChar_pos.ne'
  have hsc : ‖sc F χ (Fintype.card α) (mat c p).toBlocks₁₁.det‖ₑ ^ 2 = ((D ^ Fintype.card α : NNReal) : ENNReal) := by
    have := hnorm (Matrix.GeneralLinearGroup.det A)
    have hd : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = (mat c p).toBlocks₁₁.det := rfl
    rw [hd] at this
    rw [enorm_eq_nnnorm, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.eq
    push_cast
    rw [this]
    rfl
  have hpt : ∀ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 =
      ((D ^ Fintype.card α : NNReal) : ENNReal) * ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 := by
    intro x
    have hψe : ∀ t, ‖ψ t‖ₑ = 1 := fun t => by
      rw [enorm_eq_nnnorm]; simp [← NNReal.coe_eq_one, coe_nnnorm, hψ1 t]
    simp only [parFun, enorm_mul, hψe, one_mul, mul_pow, hsc, hA]
  haveI := htop
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * (A : Matrix ν ν E)
      invFun := fun x => x * ((A⁻¹ : GL ν E) : Matrix ν ν E)
      left_inv := fun x => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  have hmap : μ.map (e.toMeasurableEquiv) = ((D ^ Fintype.card α)⁻¹ : NNReal) • μ := by
    have := GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ 1 A
    have hf : (fun x : Matrix α ν E => ((1 : GL α E) : Matrix α α E) * x * (A : Matrix ν ν E)) = e.toMeasurableEquiv := by
      funext x; simp [e]
    rw [hf] at this
    rw [this, ← hD]
    simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have hl := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) e.toMeasurableEquiv (μ := μ)
  have hl' : ∫⁻ x, ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(μ.map e.toMeasurableEquiv) := hl.symm
  rw [hl', hmap, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hD0), ENNReal.coe_one, one_mul]

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqSiegelParabolicOperatorEqStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.KSp.parFun_lintegral_sq | exact GlobalTheory.KSp.parFun_lintegral_sq | (intros; apply GlobalTheory.KSp.parFun_lintegral_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFourSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFourSq
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Planch

variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

theorem e_zero {e : X → X → ℂ} (he : IsPair e) (y : X) : e 0 y = 1 := by
  have h := he.add 0 0 y
  rw [add_zero] at h
  have hn : e 0 y ≠ 0 := by
    intro h0
    have := he.norm 0 y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hn (h.symm.trans (mul_one _).symm)

theorem conj_e {e : X → X → ℂ} (he : IsPair e) (x y : X) : starRingEnd ℂ (e x y) = e (-x) y := by
  have hn : e x y ≠ 0 := by
    intro h0
    have := he.norm x y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h1 : e (-x) y * e x y = 1 := by rw [← he.add, neg_add_cancel, e_zero he]
  have h2 : starRingEnd ℂ (e x y) * e x y = 1 := by
    rw [Complex.conj_mul', he.norm]; simp
  exact mul_right_cancel₀ hn (h2.trans h1.symm)

theorem integral_four_mul (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (hG : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) (C : ℝ) (_hC : 0 < C)
    (hinv : ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) (φ : X → ℂ) (hφ : φ ∈ SB X) :
    ∫ x, four μ e φ x * starRingEnd ℂ (four μ e φ x) ∂μ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  set Φ := four μ e φ with hΦdef
  have hΦ : Φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hec : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hint : Integrable (Function.uncurry fun x y => e x y * φ y * starRingEnd ℂ (Φ x)) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hec.mul (hφ.1.continuous.comp continuous_snd)).mul
        ((Complex.continuous_conj.comp hΦ.1.continuous).comp continuous_fst)
    · apply HasCompactSupport.intro (hΦ.2.isCompact.prod hφ.2.isCompact)
      rintro ⟨x, y⟩ hxy
      simp only [Set.mem_prod, not_and_or] at hxy
      rcases hxy with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
  have hinner : ∀ y, ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ = (C : ℂ) * starRingEnd ℂ (φ y) := by
    intro y
    have h1 : ∀ x, e x y * starRingEnd ℂ (Φ x) = starRingEnd ℂ (e (-y) x * Φ x) := by
      intro x
      rw [map_mul, Planch.conj_e he, neg_neg, he.symm]
    simp_rw [h1]
    rw [integral_conj]
    have h2 := hinv φ hφ (-y)
    rw [neg_neg] at h2
    change starRingEnd ℂ (four μ e Φ (-y)) = _
    rw [h2, map_mul, Complex.conj_ofReal]
  calc ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ
      = ∫ x, ∫ y, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext x
        rw [integral_mul_const]
        rfl
    _ = ∫ y, ∫ x, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, φ y * ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext y
        rw [← integral_const_mul]
        congr 1; ext x; ring
    _ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
        simp_rw [hinner]
        rw [← integral_const_mul]
        congr 1; ext y; ring

theorem lintegral_four_sq : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro X _ _ _ _ hG μ _ e he C hC hinv φ hφ
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hΦ : four μ e φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hL : ∀ f ∈ SB X, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    intro f hf
    have h1 : Continuous f := hf.1.continuous
    have h2 : HasCompactSupport f := hf.2
    have h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
      have := h2.norm
      exact this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)
    have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
      (h1.norm.pow 2).integrable_of_hasCompactSupport h3
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; ext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hC' : ∀ f : X → ℂ, ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro f
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [Complex.mul_conj']
    push_cast; rfl
  have hk := integral_four_mul X hG μ e he C hC hinv φ hφ
  rw [hC', hC'] at hk
  have hk' : ∫ x, ‖four μ e φ x‖ ^ 2 ∂μ = C * ∫ x, ‖φ x‖ ^ 2 ∂μ := by exact_mod_cast hk
  rw [hL _ hΦ, hL _ hφ, hk', ENNReal.ofReal_mul hC.le]

end GlobalTheory.KSp.Planch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFourSqStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_four_sq_eq_mul_of_inversion : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.KSp.Planch.lintegral_four_sq | exact GlobalTheory.KSp.Planch.lintegral_four_sq | (intros; apply GlobalTheory.KSp.Planch.lintegral_four_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesL2Space
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped ENNReal NNReal

namespace GlobalTheory.KSp

theorem weil_representation_preserves_L2 : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ κ ω hKW μ' _ g φ
  obtain ⟨hfd, htr, hinv, ht2, hc, hn, htrc, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI := hfd
  haveI := hmt
  haveI := hgood.grp
  haveI := hgood.t2
  haveI := hgood.lc
  haveI := hgood.sc
  let N : SB (Matrix α ν E) → ℝ≥0∞ := fun f => ∫⁻ x, ‖(f : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ φ, N (ω g φ) = N φ}
      one_mem' := by intro φ; simp
      mul_mem' := by
        intro g h hg hh φ
        show N (ω (g * h) φ) = N φ
        rw [map_mul, Module.End.mul_apply, hg, hh]
      inv_mem' := by
        intro g hg φ
        have := hg (ω g⁻¹ φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hsieg : sieg c ν ≤ U := by
    intro p hp φ
    show N (ω p φ) = N φ
    simp only [N]
    rw [hKW.par p hp φ]
    exact GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ p hp φ
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψ1 hψne β hβs hβn
    simpa only [hβ] using this
  obtain ⟨C, hC, hfi⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have hpl := GlobalTheory.T.lintegral_four_sq_eq_mul_of_inversion (Matrix α ν E) hgood μ _ hpair C hC hfi
  have hw : ∀ φ : SB (Matrix α ν E), N (ω (weyl c ν) φ) = (‖κ‖ₑ ^ 2 * ENNReal.ofReal C) * N φ := by
    intro φ
    simp only [N]
    rw [hKW.wey φ]
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ (by simp), fou, hpl _ φ.2, mul_assoc]
  have hww : weyl c ν * weyl c ν ∈ sieg c ν := by
    rw [mem_sieg]
    show ((stdJ ν E) * (stdJ ν E)).toBlocks₂₁ = 0
    rw [stdJ_mul_stdJ]
    ext i j
    simp [toBlocks₂₁]
  obtain ⟨L, hLc, hLo, -⟩ := hgood.large ∅ isCompact_empty
  have hmem : (L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) ∈ SB (Matrix α ν E) := by
    refine ⟨?_, ?_⟩
    · have hcl : IsClopen (L : Set (Matrix α ν E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
      exact (LocallyConstant.charFn ℂ hcl).isLocallyConstant
    · exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  set φ₀ : SB (Matrix α ν E) := ⟨_, hmem⟩ with hφ₀
  have hN0 : N φ₀ = μ L := by
    simp only [N, hφ₀]
    have e : (fun x => ‖(L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) x‖ₑ ^ 2) =
        (L : Set (Matrix α ν E)).indicator 1 := by
      funext x
      by_cases hx : x ∈ (L : Set (Matrix α ν E)) <;> simp [hx]
    rw [e, lintegral_indicator_one hLo.measurableSet]
  have hpos : μ L ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
  set k : ℝ≥0∞ := ‖κ‖ₑ ^ 2 * ENNReal.ofReal C with hk
  have hkk : k * k = 1 := by
    have h1 : N (ω (weyl c ν * weyl c ν) φ₀) = N φ₀ := hsieg hww φ₀
    rw [map_mul, Module.End.mul_apply, hw, hw, ← mul_assoc, hN0] at h1
    have h2 := congrArg (· / μ L) h1
    simpa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.div_self hpos hfin] using h2
  have hk1 : k = 1 := by
    rcases lt_trichotomy k 1 with h | h | h
    · have : k * k ≤ k * 1 := by gcongr
      rw [hkk, mul_one] at this
      exact absurd this (not_le.mpr h)
    · exact h
    · have : 1 * k ≤ k * k := by gcongr
      rw [hkk, one_mul] at this
      exact absurd this (not_le.mpr h)
  have hwU : weyl c ν ∈ U := by
    intro φ
    show N (ω (weyl c ν) φ) = N φ
    rw [hw, hk1, one_mul]
  have htop : U = ⊤ := GlobalTheory.T.siegelParabolic_weylElement_generate_unitary F E c δ hE ν U hsieg hwU
  have hgU : g ∈ U := htop ▸ Subgroup.mem_top g
  have hμ' : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  rw [hμ', lintegral_smul_measure, lintegral_smul_measure]
  exact congrArg _ (hgU φ)
end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesL2SpaceStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_preserves_L2_space : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  first | exact @GlobalTheory.KSp.weil_representation_preserves_L2 | exact GlobalTheory.KSp.weil_representation_preserves_L2 | (intros; apply GlobalTheory.KSp.weil_representation_preserves_L2 <;> assumption)
end
