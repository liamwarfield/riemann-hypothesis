module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare
open scoped TensorProduct ContDiff Topology Pointwise

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem taylor_bound {φ φ' φ'' : ℝ → ℂ} (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) {C : ℝ}
    (hC : ∀ s, ‖φ'' s‖ ≤ C) {t : ℝ} (ht : 0 < t) : ‖(t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0‖ ≤ C * t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have a : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖φ' s - φ' 0‖ ≤ C * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (h2 s).hasDerivWithinAt) fun s _ => hC s
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => φ s - (s : ℂ) * φ' 0) (φ' s - φ' 0) s := fun s => by
    have := (h1 s).sub ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (φ' 0))
    rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at this
    exact this
  have b := norm_image_sub_le_of_norm_deriv_le_segment' (C := C * t) (a := 0) (b := t)
    (fun s _ => (d s).hasDerivWithinAt) (fun s hs => (a s ⟨hs.1, hs.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hC0)) t ⟨ht.le, le_rfl⟩
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have e : (t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0 = (t : ℂ)⁻¹ * (φ t - t * φ' 0 - (φ 0 - ((0 : ℝ) : ℂ) * φ' 0)) := by
    field_simp
    simp
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_mul_le_iff₀ ht]
  linarith

theorem eq_zero_of_lintegral_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure]
    (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (f : G → ℂ) (hf : Continuous f)
    (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) (h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0) : f = 0 := by
  have ho : IsOpen {w | f w ≠ 0} := isOpen_ne_fun hf continuous_const
  have h1 := (lintegral_eq_zero_iff (hf.measurable.enorm.pow_const 2)).1 h0
  have h2 : μ ({w | f w ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply ho.measurableSet]
    refine measure_mono_null (fun w hw => ?_) h1
    simpa using hw
  have h3 := h𝓕.measure_zero_of_invariant _ (fun γ => by
    ext w
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show f (((-γ : Γ) : G) + w) ≠ 0 ↔ f w ≠ 0
    rw [← norm_ne_zero_iff, hp _ (-γ).2, norm_ne_zero_iff]) h2
  have h4 := (ho.measure_eq_zero_iff μ).1 h3
  funext w
  by_contra hw
  exact (Set.eq_empty_iff_forall_notMem.1 h4) w hw

theorem lintegral_eq_zero_of_approx {G : Type} [MeasurableSpace G] (ν : Measure G) (hν : ν Set.univ = 1) (δ : G → ℂ)
    (C C' : ℝ) (h : ∀ t : ℝ, 0 < t → ∃ a b r : G → ℂ, δ = a - b ∧ ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ∧
      (∀ w, ‖r w‖ ≤ C * t) ∧ ∀ w, ‖b w‖ ≤ C' * t) : ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν = 0 := by
  have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have key : ∀ t : ℝ, 0 < t → ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) := by
    intro t ht
    obtain ⟨a, b, r, e, h1, h2, h3⟩ := h t ht
    have h4 : ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((C * t) ^ 2) := by
      refine (lintegral_mono (g := fun _ => ENNReal.ofReal ((C * t) ^ 2)) fun w => ?_).trans ?_
      · show ‖r w‖ₑ ^ 2 ≤ _
        rw [en]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h2 w) 2)
      · rw [lintegral_const, hν, mul_one]
    calc ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ∫⁻ w, (2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)) ∂ν := by
          refine lintegral_mono fun w => ?_
          show ‖δ w‖ₑ ^ 2 ≤ 2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)
          rw [en, en, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h5 : ‖δ w‖ ≤ ‖a w‖ + ‖b w‖ := by rw [e]; exact norm_sub_le _ _
          have h6 := pow_le_pow_left₀ (norm_nonneg _) h5 2
          have h7 := pow_le_pow_left₀ (norm_nonneg _) (h3 w) 2
          nlinarith [sq_nonneg (‖a w‖ - ‖b w‖)]
      _ = 2 * ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num), lintegral_const, hν, mul_one]
      _ ≤ 2 * ENNReal.ofReal ((C * t) ^ 2) + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [h1]; gcongr
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (p := 2) (q := (C * t) ^ 2) (by norm_num),
            ENNReal.ofReal_ofNat]
  have hc : Continuous fun t : ℝ => ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, ENNReal.ofReal_zero] at ht
  exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)) bot_le

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem theta_norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem theta_bounded (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hc w
  rw [← theta_norm_periodic hψ hf γ hγ w]
  exact hC _ h

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h : symplOH S T w 0 = 0 := by
    have := symplOH_add_right w 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  unfold heisO
  rw [h, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem quotient_bound (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ w,
      ‖((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f) - dLine ψ S T L f) w‖ ≤ C * t := by
  have h1 := theta_dLine hθ hψ hL hf
  obtain ⟨C, hC⟩ := theta_bounded hψ (theta_dLine hθ hψ hL h1)
  refine ⟨C, fun t ht w => ?_⟩
  have := taylor_bound (hasDerivAt_heisO hθ hψ hL hf w) (hasDerivAt_heisO hθ hψ hL h1 w) (C := C) (fun s => by
    unfold heisO
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hC _) ht
  rw [L.map_zero, heisO_zero, heisO_zero] at this
  exact this

variable {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hom.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hc
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hf' := hom.om_pres (g, h) f hf
  have hδ := theta_sub (theta_dLine hθ hψ hL' hf') (hom.om_pres (g, h) _ (theta_dLine hθ hψ hL hf))
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C', hC'⟩ := quotient_bound hθ hψ hL' hf'
  refine (sub_eq_zero.1 (eq_zero_of_lintegral_eq_zero (G := WA T S) (ratL T S) μ 𝓕 h𝓕 _ hδ.cont
    (theta_norm_periodic hψ hδ) ?_)).symm
  refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) (by rw [Measure.restrict_apply_univ, h1]) _ C C' fun t ht => ?_
  have theta_smul_local (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
      IsThetaFunO ψ S T (c • f) := by
    refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
    · intro γ w
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    ·
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    · intro k L h1 h2 w
      exact contDiff_const.mul (hf.smooth k L h1 h2 w)
  have hr := theta_sub (theta_smul_local (t : ℂ)⁻¹ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf))
    (theta_dLine hθ hψ hL hf)
  refine ⟨_, _, _, ?_, hom.om_unit μ 𝓕 hμ h𝓕 (g, h) _ hr, hC t ht, hC' t ht⟩
  rw [map_sub, map_smul, map_sub, hom.om_heis g h _ f hf, hLL]
  abel

theorem isLineAt_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

theorem isRealDir_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    IsRealDir T S (lineAt θ τ z) := ⟨(isLineAt_lineAt hθ τ z).1, (isLineAt_lineAt hθ τ z).2.1⟩

theorem compAt_mul (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_mul_inv (τ : D.what₂.Tau) (g : GA D S) : compAt θ τ (mt S g) * compAt θ τ (mt S g⁻¹) = 1 := by
  have e : mt S g * mt S g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← compAt_mul]
  erw [e]
  exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)

theorem lineAt_move (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T :=
    { toFun := fun t => actO S T g h (lineAt θ τ z t)
      map_zero' := by unfold actO; rw [AddMonoidHom.map_zero, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold actO; rw [AddMonoidHom.map_add (f := _), Matrix.mul_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) L := by
    refine ⟨(continuous_const.matrix_mul hL.1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, hL.2.1, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      unfold actO
      rw [compAt_mul, compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

theorem theta_dRho (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) :=
  theta_dLine hθ hψ (isRealDir_lineAt hθ τ z) hf

theorem om_dRho (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hom hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _) (lineAt_move hθ g h τ z) hf

end GlobalTheory.OrientedHeis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

open GlobalTheory.WeilVacMove

theorem eq_one_of_pow_near {z : ℂ} (hz : ‖z‖ = 1) (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1) : z = 1 := by
  by_contra hne
  have hb : ∀ n : ℕ, (n : ℝ) / 2 ≤ (∑ k ∈ Finset.range n, z ^ k).re := by
    intro n
    rw [Complex.re_sum]
    have hk : ∀ k ∈ Finset.range n, (1 / 2 : ℝ) ≤ (z ^ k).re := by
      intro k _
      have h1 : ‖z ^ k‖ ^ 2 = 1 := by rw [norm_pow, hz, one_pow, one_pow]
      have h2 : ‖z ^ k - 1‖ ^ 2 < 1 := by nlinarith [h k, norm_nonneg (z ^ k - 1)]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1 h2
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h2
      nlinarith
    have := Finset.card_nsmul_le_sum _ _ _ hk
    rw [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  have h3 : (∑ k ∈ Finset.range n, z ^ k).re ≤ 1 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [geom_sum_eq hne, norm_div]
    exact div_le_div_of_nonneg_right (h n).le hp.le
  have h4 := hb n
  have h5 : 2 / ‖z - 1‖ = 2 * (1 / ‖z - 1‖) := by ring
  linarith

theorem eventually_fin_eq_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∀ᶠ c : Af F in 𝓝 0, ψ (pairA F 0 c) = 1 := by
  have hp : Continuous fun α : Af F => pairA F 0 α := continuous_const.prodMk continuous_id
  have hc : Continuous fun α : Af F => ‖ψ (pairA F 0 α) - 1‖ := ((hψ.1.comp hp).sub continuous_const).norm
  have h0 : ‖ψ (pairA F 0 0) - 1‖ < 1 := by
    have : pairA F 0 0 = 0 := rfl
    rw [this, AddChar.map_zero_eq_one, sub_self, norm_zero]
    exact one_pos
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F {α | ‖ψ (pairA F 0 α) - 1‖ < 1}
    ((isOpen_lt hc continuous_const).mem_nhds h0)
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  refine eq_one_of_pow_near (hψ.2.1 _) fun k => ?_
  have e : pairA F 0 (N • k • a) = k • pairA F 0 (N • a) :=
    Prod.ext (smul_zero k).symm (smul_comm N k a)
  have h1 : ‖ψ (pairA F 0 (N • k • a)) - 1‖ < 1 := h (k • a) fun v => nsmul_mem (ha v) k
  rwa [e, AddChar.map_nsmul_eq_pow] at h1

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def annSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T) : AddSubgroup (WO S T) where
  carrier := {u | ψ (symplOH S T u a) = 1 ∧ ψ (symplOH S T a u) = 1}
  zero_mem' := ⟨by rw [symplOH_zero_left, AddChar.map_zero_eq_one],
    by rw [symplOH_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' hx hy := ⟨by rw [symplOH_add_left, AddChar.map_add_eq_mul, hx.1, hy.1, one_mul],
    by rw [symplOH_add_right, AddChar.map_add_eq_mul, hx.2, hy.2, one_mul]⟩
  neg_mem' {x} hx := by
    constructor
    · have : ψ (symplOH S T (-x + x) a) = 1 := by rw [neg_add_cancel, symplOH_zero_left, AddChar.map_zero_eq_one]
      rwa [symplOH_add_left, AddChar.map_add_eq_mul, hx.1, mul_one] at this
    · have : ψ (symplOH S T a (-x + x)) = 1 := by rw [neg_add_cancel, symplOH_zero_right, AddChar.map_zero_eq_one]
      rwa [symplOH_add_right, AddChar.map_add_eq_mul, hx.2, mul_one] at this

theorem isOpen_annSub (hψ : IsCharAF D.host.F ψ) {a : WO S T} (ha : a.map (infPart D) = 0) :
    IsOpen (annSub ψ S T a : Set (WO S T)) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  refine (annSub ψ S T a).isOpen_of_mem_nhds (g := 0) ?_
  have key : ∀ φ : WO S T → AF D.host.F, Continuous φ → φ 0 = 0 → (∀ u, fstA D.host.F (φ u) = 0) →
      ∀ᶠ u in 𝓝 (0 : WO S T), ψ (φ u) = 1 := by
    intro φ hφ h0 h1
    have hc : Continuous fun u => sndA D.host.F (φ u) := continuous_snd.comp hφ
    have ht : Filter.Tendsto (fun u => sndA D.host.F (φ u)) (𝓝 0) (𝓝 0) :=
      hc.tendsto' 0 0 (by rw [h0, map_zero])
    refine (ht.eventually (eventually_fin_eq_one hψ)).mono fun u hu => ?_
    have e : pairA D.host.F 0 (sndA D.host.F (φ u)) = φ u := Prod.ext (h1 u).symm rfl
    rwa [e] at hu
  exact (key (fun u => symplOH S T u a) (continuous_symplOH S T continuous_id continuous_const)
      (symplOH_zero_left S T a) fun u => fst_symplOH S T u a (Or.inr ha)).and
    (key (fun u => symplOH S T a u) (continuous_symplOH S T continuous_const continuous_id)
      (symplOH_zero_right S T a) fun u => fst_symplOH S T a u (Or.inl ha))

theorem isTheta_heisO_fin (hψ : IsCharAF D.host.F ψ) {a : WO S T} (ha : a.map (infPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T a f) := {
  quasi := heisO_quasi ψ S T a f hf.quasi
  level := by
    obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U ⊓ annSub ψ S T a, hU.inter (isOpen_annSub hψ ha), fun u hu h0 => ?_⟩
    have h2 : ψ (symplOH S T u a) = 1 ∧ ψ (symplOH S T a u) = 1 := hu.2
    conv_rhs => rw [← h1 u hu.1 h0]
    rw [heisO_heisO, heisO_heisO, h2.1, h2.2, add_comm]
  cont := by
    haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
    exact (hψ.1.comp (continuous_symplOH S T continuous_id continuous_const)).mul
      (hf.cont.comp (continuous_id.add continuous_const))
  smooth k L h1 h2 w := by
    have e : (fun t => heisO ψ S T a f (w + L t)) = fun t => ψ (symplOH S T w a) * f (w + a + L t) := by
      funext t
      rw [heisO, symplOH_add_left, (symplOH_fin_real S T a (L t) ha (h2 t)).2, add_zero, add_right_comm]
    rw [e]
    exact contDiff_const.mul (hf.smooth k L h1 h2 (w + a)) }

theorem isTheta_sum_heisO_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ), (∀ i ∈ s, (a i).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ i ∈ s, c i • heisO ψ S T (a i) f) := by
  intro D ψ S T hψ f hf ι s a c ha
  exact Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => isTheta_add) isTheta_zero
    fun i hi => isTheta_smul _ (isTheta_heisO_fin hψ (ha i hi) hf)

end GlobalTheory.FinTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousHomDifferentiable
namespace GlobalTheory.ContinuousHomDifferentiable

open intervalIntegral

theorem exists_integral_ne_zero (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) :
    ∃ δ : ℝ, (∫ x in (0:ℝ)..δ, χ x) ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, χ x) (χ 0) 0 :=
    (hc.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hfun : (fun u => ∫ x in (0:ℝ)..u, χ x) = fun _ => (0:ℂ) := funext h
  rw [hfun] at h1
  have h2 : HasDerivAt (fun _ : ℝ => (0:ℂ)) 0 0 := hasDerivAt_const _ _
  have := h1.unique h2
  rw [h0] at this
  exact one_ne_zero this

theorem continuous_hom_differentiable :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ (0 : ℝ) = (1 : ℂ) →
      (∀ (s t : ℝ), χ (s + t) = χ s * χ t) → Differentiable ℝ χ := by
  intro χ hc h0 hmul
  obtain ⟨δ, hδ⟩ := exists_integral_ne_zero χ hc h0
  set c : ℂ := ∫ x in (0:ℝ)..δ, χ x with hcdef
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, χ x with hF
  have hFd : Differentiable ℝ F := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have key : ∀ s, χ s = c⁻¹ * (F (s + δ) - F s) := by
    intro s
    have e1 : χ s * c = ∫ x in (0:ℝ)..δ, χ (s + x) := by
      rw [hcdef, ← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      rw [hmul]
    have e2 : (∫ x in (0:ℝ)..δ, χ (s + x)) = ∫ x in s..s + δ, χ x := by
      rw [intervalIntegral.integral_comp_add_left (fun x => χ x) s]
      simp
    have e3 : F (s + δ) - F s = ∫ x in s..s + δ, χ x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    rw [e3, ← e2, ← e1]
    field_simp
  have hfun : χ = fun s => c⁻¹ * (F (s + δ) - F s) := funext key
  rw [hfun]
  fun_prop

end GlobalTheory.ContinuousHomDifferentiable
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTranslate

open GlobalTheory.SplitScalar GlobalTheory.LatVac

theorem differentiable_of_char (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1)
    (hm : ∀ s t, χ (s + t) = χ s * χ t) : Differentiable ℝ χ := by
  first
  | exact @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | (apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable ..)

variable {D : D7}

theorem differentiable_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (L : ℝ →+ WO S T) (hL : Continuous L) (hfin : ∀ t, (L t).map (finPart D) = 0)
    (w : WO S T) : Differentiable ℝ fun t : ℝ => heisO ψ S T (L t) f w := by
  have h1 : Differentiable ℝ fun t : ℝ => ψ (symplOH S T w (L t)) := by
    refine differentiable_of_char _ (hψ.comp (continuous_const.mul (continuous_symplO S T continuous_const hL))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add (f := _), symplOH_add_right, AddChar.map_add_eq_mul]
  have h2 := hf.smooth 1 (L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)) (hL.comp (continuous_apply 0))
    (fun t => hfin _) w
  have h3 : Differentiable ℝ fun t : ℝ => f (w + L t) :=
    (h2.differentiable (by simp)).comp (differentiable_pi.2 fun _ : Fin 1 => differentiable_id)
  exact h1.mul h3

theorem dRho_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {ι : Type} (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ) (ha : ∀ i ∈ s, (a i).map (infPart D) = 0) :
    dRho (heisO ψ S T) θ τ z (∑ i ∈ s, c i • heisO ψ S T (a i) f) =
      ∑ i ∈ s, c i • heisO ψ S T (a i) (dRho (heisO ψ S T) θ τ z f) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ z)
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) =
      fun t : ℝ => ∑ i ∈ s, (c i * ψ (symplOH S T x (a i))) * heisO ψ S T (lineAt θ τ z t) f (x + a i) := by
    funext t
    rw [heisO_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [heisO_smul, heisO_comm, symplO_real_fin S T (hL.2.1 t) (ha i hi), AddChar.map_zero_eq_one, one_smul,
      mul_assoc]
    rfl
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) 0 = _
  rw [e, deriv_fun_sum fun i _ => ((differentiable_heisO hψ hf _ hL.1 hL.2.1 (x + a i)).const_mul _) 0,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deriv_const_mul_field, mul_assoc]
  rfl

theorem isFockVacAt_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsCharAF D.host.F ψ → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ), IsFockVacAt (heisO ψ S T) θ τ J f → ∀ (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ), (∀ i ∈ s, (a i).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ i ∈ s, c i • heisO ψ S T (a i) f) := by
  intro D ψ θ S T hψ hθ f hf τ J hv ι s a c ha z
  have hc : Continuous ψ := hψ.1
  have h0 : dRho (heisO ψ S T) θ τ z f + Complex.I • dRho (heisO ψ S T) θ τ (J z) f = 0 := hv z
  rw [annih, dRho_sum hc hθ hf τ z s a c ha, dRho_sum hc hθ hf τ (J z) s a c ha, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_comm, ← smul_add, ← heisO_smul, ← heisL_apply, ← heisL_apply, ← map_add (f := _), h0, map_zero, smul_zero]

end GlobalTheory.FockTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisOrtho

open GlobalTheory.SplitScalar

theorem setIntegral_add_right {G E : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → E)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

theorem integral_norm_sq_sum {X ι : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (s : Finset ι)
    (g : ι → X → ℂ) (c : ι → ℂ) (C : ℝ) (hm : ∀ i, Measurable (g i)) (hC : ∀ i x, ‖g i x‖ ≤ C)
    (hc : ∀ i ∈ s, ‖c i‖ = 1) (h1 : ∀ i ∈ s, ∫ x, ‖g i x‖ ^ 2 ∂ν = 1)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ x, g i x * (starRingEnd ℂ) (g j x) ∂ν = 0) :
    ∫ x, ‖(∑ i ∈ s, c i • g i) x‖ ^ 2 ∂ν = (s.card : ℝ) := by
  classical
  have hi : ∀ i j, Integrable (fun x => g i x * (starRingEnd ℂ) (g j x)) ν := fun i j => by
    refine Integrable.of_bound (((hm i).mul (Complex.continuous_conj.measurable.comp (hm j))).aestronglyMeasurable)
      (C * C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC i x) (hC j x) (norm_nonneg _) ((norm_nonneg _).trans (hC i x))
  have e : ∀ x, ((‖(∑ i ∈ s, c i • g i) x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * (g i x * (starRingEnd ℂ) (g j x)) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Complex.ofReal_pow, ← Complex.mul_conj', Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [e]
  rw [integral_finsetSum (f := fun i x => ∑ j ∈ s, c i * (starRingEnd ℂ) (c j) *
      (g i x * (starRingEnd ℂ) (g j x))) _
      (fun i _ => integrable_finsetSum _ fun j _ => (hi i j).const_mul _),
    Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_congr rfl fun i hi' => ?_
  rw [integral_finsetSum (f := fun j x => c i * (starRingEnd ℂ) (c j) *
      (g i x * (starRingEnd ℂ) (g j x))) _ (fun j _ => (hi i j).const_mul _),
    Finset.sum_eq_single i]
  · rw [integral_const_mul, Complex.mul_conj', hc i hi']
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, h1 i hi']
    simp
  · intro j hj hji
    rw [integral_const_mul, h0 i hi' j hj hji.symm, mul_zero]
  · exact fun h => absurd hi' h

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_quasi {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) (γ : WO S T) (hγ : γ ∈ ratL T S)
    (w : WO S T) : heisO ψ S T u f (γ + w) = ψ (-(symplOH S T γ w)) * heisO ψ S T u f w := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hf.quasi γ (w + u)
  show ψ (symplOH S T (ratW T S γ + w) u) * f (ratW T S γ + w + u) =
    ψ (-(symplOH S T (ratW T S γ) w)) * (ψ (symplOH S T w u) * f (w + u))
  rw [add_assoc, h, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    symplOH_add_left, symplOH_add_right]
  congr 2
  abel

theorem continuous_heisO (hψ : IsCharAF D.host.F ψ) {f : WO S T → ℂ} (hf : Continuous f) (u : WO S T) :
    Continuous (heisO ψ S T u f) :=
  (hψ.1.comp (continuous_const.mul (continuous_symplO S T continuous_id continuous_const))).mul
    (hf.comp (continuous_id.add continuous_const))

theorem norm_heisO (hψ : IsCharAF D.host.F ψ) (f : WO S T → ℂ) (u w : WO S T) :
    ‖heisO ψ S T u f w‖ = ‖f (w + u)‖ := by
  rw [heisO, norm_mul, hψ.2.1, one_mul]

theorem mul_conj_of_norm_one {z : ℂ} (h : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj', h]; simp

theorem thetaNormSq_sum_heisenbergTranslates_distinctChars (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsCharAF D.host.F ψ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : IsCovolOne (ratL T S) μ 𝓕) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hn : nrm2 μ 𝓕 f = 1) (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ = 1)
    (hl : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ (l : WO S T) (ε : ℂ), ‖ε‖ = 1 ∧ heisO ψ S T l f = ε • f ∧
      ψ (symplO S T (a i - a j) l) ≠ 1) :
    nrm2 μ 𝓕 (∑ i ∈ s, c i • heisO ψ S T (a i) f) = (s.card : ℝ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨hμ, h𝓕, h1⟩ := hμ
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    rintro _ ⟨γ, rfl⟩ w
    exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  have hC' : ∀ w, ‖f w‖ ≤ C := fun w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  refine integral_norm_sq_sum (μ.restrict 𝓕) s (fun i => heisO ψ S T (a i) f) c C
    (fun i => (continuous_heisO hψ hf.cont _).measurable) (fun i x => by rw [norm_heisO hψ]; exact hC' _) hc
    (fun i _ => ?_) fun i hi j hj hij => ?_
  · simp_rw [norm_heisO hψ]
    exact (setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕 (fun w => ‖f w‖ ^ 2)
      (fun γ hγ w => by simp only [hp γ hγ w]) (a i)).trans hn
  · obtain ⟨l, ε, hε, he, hne⟩ := hl i hi j hj hij
    have ev : ∀ b w, ψ (symplOH S T w l) * heisO ψ S T b f (w + l) =
        ψ (symplO S T l b) * (ε * heisO ψ S T b f w) := fun b w => by
      have := congrFun (heisO_comm ψ S T l b f) w
      rw [he, heisO_smul] at this
      exact this
    have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
      (fun w => heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) (fun γ hγ w => by
        have := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T γ w)))
        simp only [heisO_quasi hf _ γ hγ, map_mul]
        linear_combination (heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) * this) l
    have hκ : ψ (symplO S T (a i - a j) l) * (ψ (symplO S T l (a i)) * (starRingEnd ℂ) (ψ (symplO S T l (a j)))) = 1 := by
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, symplO_sub_left, symplO_skew S T l (a i), symplO_skew S T l (a j),
        show -symplO S T l (a i) - -symplO S T l (a j) + symplO S T l (a i) = symplO S T l (a j) by abel]
      exact mul_conj_of_norm_one (hψ.2.1 _)
    have e : ∀ w, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) =
        ψ (symplO S T (a i - a j) l) *
          (heisO ψ S T (a i) f (w + l) * (starRingEnd ℂ) (heisO ψ S T (a j) f (w + l))) := fun w => by
      have e1 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w l))
      have e2 := mul_conj_of_norm_one hε
      have e3 := ev (a i) w
      have e4 := congrArg (starRingEnd ℂ) (ev (a j) w)
      rw [map_mul, map_mul, map_mul] at e4
      have e5 := congrArg₂ (· * ·) e3 e4
      rw [mul_mul_mul_comm, e1, one_mul] at e5
      rw [e5, mul_mul_mul_comm (ψ _), ← mul_assoc, hκ, one_mul, mul_mul_mul_comm, e2, one_mul]
    have k2 : ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ =
        ψ (symplO S T (a i - a j) l) *
          ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ := by
      conv_rhs => rw [← key, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall e)
    have k3 : (ψ (symplO S T (a i - a j) l) - 1) *
        ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← k2, sub_self]
    exact (mul_eq_zero.1 k3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.HeisOrtho

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedFormLaws

theorem sum_mul_left {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * (x.map fun z => t * z) d a) =
      t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem sum_mul_right {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c ((y.map fun z => t * z) e b) * Q e d * x d a) =
      c t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

variable {D : D7} {S T : HSp D}

theorem hO_mul_left (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T (x.map fun z => t * z) y = t * hO S T x y :=
  sum_mul_left (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_mul_right (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T x (y.map fun z => t * z) = cA D t * hO S T x y :=
  sum_mul_right (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hO S T (M.map (incA D)) (N.map (incA D)) = incA D (GlobalTheory.LatVac.hRat S T M N) := by
  unfold hO GlobalTheory.LatVac.hRat
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, map_sum, RingHom.map_mul]

theorem symplOH_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (M.map (incA D)) (N.map (incA D)) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) := by
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [symplOH, symplO, hO_rat, ← RingHom.map_mul, h2, GlobalTheory.LatVac.trace_tmul, one_mul, RingHom.map_mul]

theorem hO_half (e : Formalism.L2.Theta.AE D) (u : WO S T) (he : e * cA D e = 0) (hu : IsHalf e u) : hO S T u u = 0 := by
  have h : (u.map fun z => e * z) = u := by
    funext i j
    exact hu i j
  have h1 := hO_mul_left e u u
  have h2 := hO_mul_right e u u
  rw [h] at h1 h2
  rw [h1, h2, ← mul_assoc, he, zero_mul]

theorem symplOH_laws : ∀ (D : D7) (S T : HSp D), (∀ x y z : WO S T, symplOH S T (x + y) z = symplOH S T x z + symplOH S T y z) ∧ (∀ x y z : WO S T, symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z) ∧ (∀ x : WO S T, symplOH S T x x = 0) ∧ (∀ x y : WO S T, symplOH S T x y + symplOH S T x y = symplO S T x y) ∧ Continuous (fun q : WO S T × WO S T => symplOH S T q.1 q.2) ∧ (∀ g ∈ ratL T S, ∀ g' ∈ ratL T S, ∃ a : D.host.F, symplOH S T g g' = algebraMap D.host.F (AF D.host.F) a) ∧ (∀ (a : AE D) (x y : WO S T), symplOH S T (x.map fun z => a * z) y = symplOH S T x (y.map fun z => cA D a * z)) ∧ (∀ (e a : AE D) (u : WO S T), e * cA D e = 0 → IsHalf e u → symplOH S T (u.map fun z => a * z) u = 0) ∧ ∀ x y : WO S T, x.map (finPart D) = 0 → y.map (infPart D) = 0 → symplOH S T x y = 0 := by
  intro D S T
  refine ⟨GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_self,
    fun x y => ?_, GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd, ?_, fun a x y => ?_,
    fun e a u he hu => ?_, fun x y hx hy => (GlobalTheory.OrientedHeis.symplOH_fin_real hy hx).2⟩
  · unfold symplOH
    rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  · rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
    exact ⟨_, symplOH_rat M N⟩
  · unfold symplOH symplO
    rw [hO_mul_left, hO_mul_right, GlobalTheory.DualPairCheck.cA_cA]
  · unfold symplOH symplO
    rw [hO_mul_left, hO_half e u he hu, mul_zero, mul_zero, LinearMap.map_zero, mul_zero]

end GlobalTheory.OrientedFormLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous : ∀ (D : D7) (S T : HSp D), (∀ x y z : WO S T, symplOH S T (x + y) z = symplOH S T x z + symplOH S T y z) ∧ (∀ x y z : WO S T, symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z) ∧ (∀ x : WO S T, symplOH S T x x = 0) ∧ (∀ x y : WO S T, symplOH S T x y + symplOH S T x y = symplO S T x y) ∧ Continuous (fun q : WO S T × WO S T => symplOH S T q.1 q.2) ∧ (∀ g ∈ ratL T S, ∀ g' ∈ ratL T S, ∃ a : D.host.F, symplOH S T g g' = algebraMap D.host.F (AF D.host.F) a) ∧ (∀ (a : AE D) (x y : WO S T), symplOH S T (x.map fun z => a * z) y = symplOH S T x (y.map fun z => cA D a * z)) ∧ (∀ (e a : AE D) (u : WO S T), e * cA D e = 0 → IsHalf e u → symplOH S T (u.map fun z => a * z) u = 0) ∧ ∀ x y : WO S T, x.map (finPart D) = 0 → y.map (infPart D) = 0 → symplOH S T x y = 0 := by
  first | exact @GlobalTheory.OrientedFormLaws.symplOH_laws | exact GlobalTheory.OrientedFormLaws.symplOH_laws | (intros; apply GlobalTheory.OrientedFormLaws.symplOH_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open GlobalTheory.Member

namespace GlobalTheory.UnRep.Space

theorem finrank_two (D : D7) : Module.finrank D.host.F D.host.E = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D.host.E) D.host.E

theorem isUnA_finHom {D : D7} (V : HSp D) (g : GA D V) : GlobalTheory.UnRep.IsUnA (cF D) V.gramᵀ (finHom V g).1 := by
  intro x y
  rw [GlobalTheory.UnitarySplit.hermA_eq, GlobalTheory.UnitarySplit.hermA_eq]
  exact (GlobalTheory.Member.RatElt.mem_UJ_iff _ _ _).1 (GlobalTheory.UnitarySplit.finHom_mem V g) y x

theorem herm_neg_eq {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) u v = -GlobalTheory.UnRep.hermE (cF D) V.gramᵀ u v := by
  unfold herm GlobalTheory.UnRep.hermE
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change u a * (-V.gram b a) * cc (v b) = -(u a * V.gram b a * cc (v b))
  ring


set_option maxHeartbeats 1000000 in
theorem exists_rep_suppSplit : ∀ (D : D7) (V : HSp D) (N : ℕ), 0 < N → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ h ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * h * k ∧ FinCong V N k ∧ GlobalTheory.UnRep.SuppSplit (cF D) N (finHom V h).1 := by
  intro D V N hN g
  obtain ⟨e1, -, hfg, hsp, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, -⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (finrank_two D) (latC V) hfg hsp (finHom V g) N (isUnA_finHom V g) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [herm_neg_eq, herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, γ⁻¹ * g * k⁻¹ * h⁻¹, ?_, h, hh, k, hk', by group, ?_, ?_⟩
  · change finHom V _ = 1
    simp only [map_mul, map_inv, e]
    group
  · unfold FinCong
    rw [e1, ek]
    exact hk
  · rw [eh]
    exact hs

end GlobalTheory.UnRep.Space
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.SymplecticOrthogonalSesquilinear

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_eq_neg {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {a : R} (h : a = -a) :
    a = 0 := by
  have h2 : (2 : F) • a = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.1 h
  exact (smul_eq_zero_iff_right two_ne_zero).1 h2

theorem map_sesq {E A : Type} [CommRing E] [CommRing A] (ι : E →+* A) (c : A →+* A) (s : E → E)
    (hc : ∀ e, c (ι e) = ι (s e)) {m n : ℕ} (ξ : E) (P : Fin m → Fin m → E) (Q : Fin n → Fin n → E)
    (x y : Fin n → Fin m → E) :
    ι ξ * ∑ a, ∑ b, ∑ c', ∑ d, ι (P a b) * c (ι (y c' b)) * ι (Q c' d) * ι (x d a) =
      ι (ξ * ∑ a, ∑ b, ∑ c', ∑ d, P a b * s (y c' b) * Q c' d * x d a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc]

theorem symplO_rat (D : D7) (S T : HSp D) (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have h : ∃ e : D.host.E, incA D D.host.xi0 * hO S T (ratW T S γ) (ratW T S γ') = incA D e :=
    ⟨_, map_sesq (incA D) (cA D) star GlobalTheory.DualPairCheck.cA_incA D.host.xi0 (fun a b => S.gram⁻¹ a b)
      (fun a b => T.gram a b) γ γ'⟩
  obtain ⟨e, he⟩ := h
  refine ⟨Algebra.trace D.host.F D.host.E e, ?_⟩
  unfold symplO
  rw [he]
  exact trace_one_tmul _ e

theorem symplO_alt : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  intro D S T
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun x y => GlobalTheory.WeilVacMove.symplO_skew S T y x,
    fun x => eq_zero_of_eq_neg (F := D.host.F) (GlobalTheory.WeilVacMove.symplO_skew S T x x), symplO_rat D S T⟩
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.SymplecticOrthogonalSesquilinear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  first | exact @GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | exact GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | (intros; apply GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt <;> assumption)
end
end
