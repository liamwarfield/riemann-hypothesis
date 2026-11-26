module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL GlobalTheory.CompanionTheory.QL.instMeasGL

noncomputable section
namespace GlobalTheory.GJTransfer

theorem det_mem_integer {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (X : Matrix (Fin n) (Fin n) k)
    (hX : X ∈ intM k (Fin n) (Fin n)) : valuation k X.det ≤ 1 := by
  let Y : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X.det = (𝒪[k].subtype.mapMatrix Y).det := rfl
  rw [e, ← RingHom.map_det]
  exact (Y.det).2

theorem integrable_volGL_of_lintegral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure]
    (n : ℕ) (σ s : ℝ) (hs : s ≤ σ - n)
    (hI : ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤) :
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ) (volGL μ (Fin n)) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have hE := Model.measurableEmbedding_val (k := k) (Fin n)
  have hd := continuous_density_volGL (k := k) (n := Fin n)
  have hn : IsLocallyConstant fun g : GL (Fin n) k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hO : IsClopen (intM k (Fin n) (Fin n)) := ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hind : IsLocallyConstant fun g : GL (Fin n) k =>
      (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℝ) hO).isLocallyConstant.comp_continuous
      Units.continuous_val
  set F : GL (Fin n) k → ℝ := fun g => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ with hF
  have hFc : Continuous F :=
    hind.continuous.mul (hn.comp fun r : ℝ => r ^ σ).continuous
  refine ⟨hFc.aestronglyMeasurable, ?_⟩
  set I : Matrix (Fin n) (Fin n) k → ENNReal := (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) with hIdef
  have hpt : ∀ g : GL (Fin n) k, ENNReal.ofReal (nabs k (GeneralLinearGroup.det g) ^ (-(Fintype.card (Fin n) : ℝ)))
      * ‖F g‖ₑ ≤ I g.val := by
    intro g
    have hp := nabs_pos' (GeneralLinearGroup.det g)
    set a := nabs k (GeneralLinearGroup.det g) with ha
    by_cases hg : g.val ∈ intM k (Fin n) (Fin n)
    · have h0 : (g.val).det ≠ 0 := g.det_ne_zero
      have hu : Units.mk0 (g.val).det h0 = GeneralLinearGroup.det g := Units.ext rfl
      have hle : a ≤ 1 := by
        rw [ha, ← hu]
        exact Model.nabs_le_one _ (det_mem_integer _ hg)
      rw [hIdef, Set.indicator_of_mem hg, dite_eq_right h0, hu, ← ha, ENNReal.ofReal_rpow_of_pos hp]
      have hFg : F g = a ^ σ := by
        rw [hF]; simp only [Set.indicator_of_mem hg, one_mul]; rfl
      rw [hFg, Real.enorm_of_nonneg (Real.rpow_nonneg hp.le _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _), ← Real.rpow_add hp, Fintype.card_fin]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hp hle ?_)
      linarith
    · have hFg : F g = 0 := by
        rw [hF]; simp only [Set.indicator_of_notMem hg, zero_mul]
      rw [hFg]; simp
  unfold HasFiniteIntegral volGL
  erw [lintegral_withDensity_eq_lintegral_mul _ hd.measurable hFc.enorm.measurable]
  calc _ ≤ ∫⁻ g : GL (Fin n) k, I g.val ∂((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val) :=
        lintegral_mono fun g => hpt g
    _ = ∫⁻ X, I X ∂(((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val).map
          fun g : GL (Fin n) k => g.val) := (hE.lintegral_map I).symm
    _ = ∫⁻ X, I X ∂((volM μ (Fin n) (Fin n)).restrict (Set.range fun g : GL (Fin n) k => g.val)) := by
        erw [hE.map_comap]; rfl
    _ ≤ ∫⁻ X, I X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hI

theorem integrable_haarVol_of_lintegral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ s : ℝ) (hs : s ≤ σ - n)
    (hI : ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X
        ∂(volM (Measure.addHaar : Measure k) (Fin n) (Fin n)) < ⊤) :
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : SecondCountableTopology (GL (Fin n) k) := secondCountable_GL
  have : (volGL (Measure.addHaar : Measure k) (Fin n)).IsHaarMeasure := isHaarMeasure_volGL _
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  rw [Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin n))) (volGL (Measure.addHaar : Measure k) (Fin n))]
  exact (integrable_volGL_of_lintegral _ n σ s hs hI).smul_measure_nnreal

end GlobalTheory.GJTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFinite
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

noncomputable section
namespace GlobalTheory.IntShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow' (u : kˣ) (m : ℕ) : nabs k (u ^ m) = nabs k u ^ m := by
  simp [nabs, map_pow]

theorem exists_unit_nabs_lt_one : ∃ u : kˣ, nabs k u < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  refine ⟨Units.mk0 _ h0, ?_⟩
  rw [nabs_uniformiser hϖ rfl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)

theorem cball_one : cball (1 : kˣ) = (𝒪[k] : Set k) := by
  ext y; simp [cball, Valuation.mem_integer_iff]

theorem nabs_le_of_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∈ cball u) :
    nabs k (Units.mk0 y hy) ≤ nabs k u := by
  rw [nabs_le_iff]; exact h

theorem nabs_ge_of_not_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∉ cball u) :
    nabs k u ≤ nabs k (Units.mk0 y hy) := by
  rw [nabs_le_iff]; exact (not_le.mp h).le

theorem exists_shell {u : kˣ} (hu : nabs k u < 1) {y : k} (hy : y ≠ 0) (hO : y ∈ 𝒪[k]) :
    ∃ m : ℕ, y ∈ cball (u ^ m) ∧ y ∉ cball (u ^ (m + 1)) := by
  have hP : ∃ n : ℕ, y ∉ cball (u ^ n) := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (nabs_pos k (Units.mk0 y hy)) hu
    refine ⟨n, fun h => ?_⟩
    have := nabs_le_of_mem_cball hy h
    rw [nabs_pow'] at this
    linarith
  have h0 : Nat.find hP ≠ 0 := by
    intro h
    have := Nat.find_spec hP
    rw [h, pow_zero, cball_one] at this
    exact this hO
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  refine ⟨m, ?_, ?_⟩
  · have := Nat.find_min hP (show m < Nat.find hP by omega)
    simpa using this
  · have := Nat.find_spec hP
    rwa [hm] at this

section Meas
variable [MeasurableSpace k] [BorelSpace k]

theorem measure_zero_singleton (μ : Measure k) [μ.IsAddHaarMeasure] : μ {0} = 0 := by
  obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
  have hle : ∀ m : ℕ, μ {0} ≤ ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k) := by
    intro m
    have h1 : ({0} : Set k) ⊆ cball (u ^ m) := by
      intro y hy; rw [Set.mem_singleton_iff.mp hy]; simp [cball]
    refine (measure_mono h1).trans (le_of_eq ?_)
    rw [measure_cball, map_pow]
    congr 1
    simp [nabs, ENNReal.ofReal_coe_nnreal]
  have ht : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k)) Filter.atTop
      (nhds (0 * μ (𝒪[k] : Set k))) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by rw [ENNReal.ofReal_lt_one]; exact hu)) (Or.inr (isCompact_int k).measure_lt_top.ne)
  rw [zero_mul] at ht
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

end Meas

section Main
variable [MeasurableSpace k] [BorelSpace k]

theorem lintegral_int_nabs_rpow_lt_top (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ) (hs : -1 < s) :
    ∫⁻ x, (𝒪[k] : Set k).indicator
      (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ < ⊤ := by
  have hO : μ (𝒪[k] : Set k) < ⊤ := (isCompact_int k).measure_lt_top
  rcases le_or_gt 0 s with hs0 | hs0
  · calc _ ≤ ∫⁻ x, (𝒪[k] : Set k).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
            refine ENNReal.rpow_le_one ?_ hs0
            rw [ENNReal.ofReal_le_one]
            split_ifs with h
            · exact zero_le_one
            · exact Model.nabs_le_one _ hx
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      _ = μ (𝒪[k] : Set k) := by rw [lintegral_indicator_const (isOpen_int k).measurableSet, one_mul]
      _ < ⊤ := hO
  ·
    obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
    set R := ENNReal.ofReal (nabs k u) with hRdef
    have hR0 : R ≠ 0 := by rw [hRdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact nabs_pos k u
    have hRt : R ≠ ⊤ := ENNReal.ofReal_ne_top
    have hR1 : R ^ s * R < 1 := by
      have e : R ^ s * R = R ^ (s + 1) := by rw [ENNReal.rpow_add _ _ hR0 hRt, ENNReal.rpow_one]
      rw [e]
      exact ENNReal.rpow_lt_one (by rw [hRdef, ENNReal.ofReal_lt_one]; exact hu) (by linarith)
    have hRs : R ^ s < ⊤ := by
      rw [lt_top_iff_ne_top, ne_eq, ENNReal.rpow_eq_top_iff]
      rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hR0 h
      · exact hRt h
    have hanti : ∀ a b : ℝ≥0∞, a ≤ b → b ^ s ≤ a ^ s := by
      intro a b h
      have hb : b ^ s = (b ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      have ha : a ^ s = (a ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      rw [ha, hb]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow h (show (0:ℝ) ≤ -s by linarith))
    have hae : ∀ᵐ y ∂μ, y ∉ ({0} : Set k) := measure_eq_zero_iff_ae_notMem.mp (measure_zero_singleton μ)
    calc _ ≤ ∫⁻ y, ∑' m : ℕ, (cball (u ^ m)).indicator
            (fun _ => ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s) y ∂μ := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          have hy0 : y ≠ 0 := hy
          by_cases hx : y ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, dite_eq_right hy0]
            obtain ⟨m, hm1, hm2⟩ := exists_shell hu hy0 hx
            refine le_trans ?_ (ENNReal.le_tsum m)
            rw [Set.indicator_of_mem hm1]
            refine hanti _ _ (ENNReal.ofReal_le_ofReal ?_)
            have := nabs_ge_of_not_mem_cball hy0 hm2
            rwa [nabs_pow'] at this
          · rw [Set.indicator_of_notMem hx]; exact bot_le
      _ = ∑' m : ℕ, ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s * μ (cball (u ^ m)) := by
          rw [lintegral_tsum fun m => (measurable_const.indicator (isOpen_cball _).measurableSet).aemeasurable]
          congr 1; funext m
          rw [lintegral_indicator_const (isOpen_cball _).measurableSet]
      _ = ∑' m : ℕ, R ^ s * μ (𝒪[k] : Set k) * (R ^ s * R) ^ m := by
          congr 1; funext m
          have hc : ((distribHaarChar k (u ^ m) : NNReal) : ℝ≥0∞) = R ^ m := by
            rw [map_pow, ENNReal.coe_pow, hRdef]
            congr 1
            simp [nabs, ENNReal.ofReal_coe_nnreal]
          have h2 : ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s = (R ^ s) ^ m * R ^ s := by
            rw [ENNReal.ofReal_pow (nabs_pos k u).le, ← hRdef, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
              mul_comm (((m + 1 : ℕ)) : ℝ) s, ENNReal.rpow_mul, ENNReal.rpow_natCast, pow_succ]
          rw [h2, measure_cball, hc, mul_pow]
          ring
      _ = R ^ s * μ (𝒪[k] : Set k) * (1 - R ^ s * R)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hRs hO) ?_
          rw [ENNReal.inv_lt_top]
          exact tsub_pos_of_lt hR1

end Main

end GlobalTheory.IntShell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFiniteStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_abs_pow_integers_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), -1 < s →
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ < ⊤ := by
  first | exact @GlobalTheory.IntShell.lintegral_int_nabs_rpow_lt_top | exact GlobalTheory.IntShell.lintegral_int_nabs_rpow_lt_top | (intros; apply GlobalTheory.IntShell.lintegral_int_nabs_rpow_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit.CornerFubini

theorem lintegral_prod_le_symm {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_prod_swap]
  exact lintegral_prod_le _

theorem lintegral_cons_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (n : ℕ)
    (G : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ u, ∫⁻ x, G (Fin.cons x u) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  rw [h.lintegral_map_equiv G _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_col_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (m n : ℕ)
    (G : (Fin m → Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ M, ∫⁻ v, G (fun i => Fin.cons (v i) (M i)) ∂(Measure.pi fun _ : Fin m => μ)
        ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : Fin m => e)
      (Measure.pi fun _ : Fin m => μ.prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) :=
    measurePreserving_pi _ _ (f := fun _ : Fin m => e) (fun _ => h)
  have h2 := (measurePreserving_arrowProdEquivProdArrow α (Fin n → α) (Fin m) (fun _ => μ)
    (fun _ => Measure.pi fun _ : Fin n => μ)).symm
  rw [h1.lintegral_map_equiv G _, h2.lintegral_map_equiv _ _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  refine lintegral_congr fun M => lintegral_congr fun v => congrArg G ?_
  funext i
  change e (v i, M i) = _
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_volM_le_corner (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ)
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞) :
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  refine (lintegral_cons_le (Measure.pi fun _ : Fin (n + 1) => ν) n F).trans ?_
  refine (lintegral_col_le ν n n _).trans ?_
  refine lintegral_mono fun M => lintegral_mono fun v => ?_
  exact lintegral_cons_le ν n
    (fun r => F (Matrix.of (Fin.cons r (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))))

end GlobalTheory.KSplit.CornerFubini
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumnStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_matrix_first_row_column : ∀ (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ) (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞),
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  first | exact @GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | exact GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | (intros; apply GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit

section OneVar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_mul_of_ne_zero {s : ℝ} (hs : s < 0) {a : k} (ha : a ≠ 0) (y : k) :
    ENNReal.ofReal (if h : a * y = 0 then 0 else nabs k (Units.mk0 (a * y) h)) ^ s =
      ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s *
        ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s := by
  have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
    simpa using Model.nabs_pos _
  by_cases hy : y = 0
  · subst hy
    have : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hpa]
    simp [ENNReal.zero_rpow_of_neg hs, ENNReal.mul_top this]
  · have hay : a * y ≠ 0 := mul_ne_zero ha hy
    have hpy : ENNReal.ofReal (nabs k (Units.mk0 y hy)) ≠ 0 := by
      simpa using Model.nabs_pos _
    have e : Units.mk0 (a * y) hay = Units.mk0 a ha * Units.mk0 y hy := Units.ext rfl
    rw [dite_eq_right hay, dite_eq_right hy, e, Model.nabs_mul, ENNReal.ofReal_mul (Model.nabs_pos _).le,
      ENNReal.mul_rpow_of_ne_zero hpa hpy]

theorem absPow_le_one_of_notMem [MeasurableSpace k] [BorelSpace k] {s : ℝ} (hs : s < 0) {y : k} (hy : y ∉ 𝒪[k]) :
    ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s ≤ 1 := by
  have h0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  rw [dite_eq_right h0]
  refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ hs
  have h1 : valuation k y⁻¹ ≤ 1 := ((valuation k).val_le_one_or_val_inv_le_one y).resolve_left hy
  have h2 : nabs k (Units.mk0 y h0)⁻¹ ≤ 1 := Model.nabs_le_one _ (by simpa using h1)
  have h3 : nabs k (Units.mk0 y h0) * nabs k (Units.mk0 y h0)⁻¹ = 1 := by
    rw [← Model.nabs_mul, mul_inv_cancel, Model.nabs_one]
  have h4 := Model.nabs_pos (Units.mk0 y h0)
  rw [ENNReal.one_le_ofReal]
  nlinarith

end OneVar

theorem lintegral_absPow_affine_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ)
    (hs : s < 0) (a b : k) :
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  have hO : IsOpen (𝒪[k] : Set k) := Model.isOpen_int
  by_cases ha : a = 0
  · have hpos : μ (𝒪[k] : Set k) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
    rw [dite_eq_left ha, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hs, ENNReal.top_mul]
    · exact le_top
    · exact fun h => hpos (add_eq_zero.1 h).2
  rw [dite_eq_right ha]
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  set C : ℝ≥0∞ := ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s with hC
  have hCt : C ≠ ⊤ := by
    have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
      simpa using Model.nabs_pos _
    simp [hC, ENNReal.rpow_eq_top_iff, hpa]
  have hpt : ∀ x, (𝒪[k] : Set k).indicator (fun y => P (a * y + b)) x ≤
      C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) := by
    intro x
    by_cases hx : x ∈ (𝒪[k] : Set k)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have e : a * x + b = a * (x + b / a) := by field_simp
      have e' : P (a * x + b) = C * P (x + b / a) := by
        rw [e]; exact absPow_mul_of_ne_zero hs ha _
      rw [e']
      gcongr
      by_cases hx' : x + b / a ∈ (𝒪[k] : Set k)
      · rw [Set.indicator_of_mem hx']; exact le_self_add
      · rw [Set.indicator_of_notMem hx', zero_add]; exact absPow_le_one_of_notMem hs hx'
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  calc _ ≤ ∫⁻ x, C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ hCt,
          lintegral_add_right _ (measurable_one.indicator hO.measurableSet),
          lintegral_add_right_eq_self (fun x => (𝒪[k] : Set k).indicator P x),
          lintegral_indicator_one hO.measurableSet]

end GlobalTheory.KSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBoundStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_affine_abs_pow_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), s < 0 → ∀ a b : k,
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  first | exact @GlobalTheory.KSplit.lintegral_absPow_affine_le | exact GlobalTheory.KSplit.lintegral_absPow_affine_le | (intros; apply GlobalTheory.KSplit.lintegral_absPow_affine_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.GJInt

theorem det_blk {k : Type} [Field k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det =
      x * M.det + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det := by
  rw [det_succ_row_zero, det_succ_row_zero (Matrix.of _), Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Matrix.submatrix]
  exact Or.inl rfl

theorem mem_intM_blk {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))) ∈ intM k (Fin (n + 1)) (Fin (n + 1)) ↔
      x ∈ 𝒪[k] ∧ (∀ j, u j ∈ 𝒪[k]) ∧ (∀ i, v i ∈ 𝒪[k]) ∧ M ∈ intM k (Fin n) (Fin n) := by
  simp only [intM, Set.mem_setOf_eq, Fin.forall_fin_succ, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, forall_and]
  tauto

theorem det_mem_int {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {X : Matrix (Fin n) (Fin n) k}
    (hX : X ∈ intM k (Fin n) (Fin n)) : X.det ∈ 𝒪[k] := by
  have h1 := (𝒪[k].subtype).map_det (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k]))
  have h2 : (𝒪[k].subtype).mapMatrix (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k])) = X := by ext; rfl
  rw [h2] at h1
  rw [← h1]
  exact SetLike.coe_mem _

theorem intdet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  intro k _ _ _ _ _ _ μ _ n s hs
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hOm : MeasurableSet (𝒪[k] : Set k) := GlobalTheory.SplitWeil.Model.isOpen_int.measurableSet
  have hO : μ (𝒪[k] : Set k) ≠ ⊤ := GlobalTheory.SplitWeil.Model.isCompact_int.measure_lt_top.ne
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  show ∫⁻ X, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ∂(volM μ (Fin n) (Fin n)) < ⊤
  rcases le_or_gt 0 s with hs0 | hs0
  · have hb : ∀ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ≤
        (intM k (Fin n) (Fin n)).indicator 1 X := by
      intro X
      by_cases hX : X ∈ intM k (Fin n) (Fin n)
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
        have hdet := det_mem_int hX
        simp only [P, Pi.one_apply]
        split_ifs with h
        · rcases hs0.eq_or_lt with h0 | h0
          · simp [← h0]
          · simp [ENNReal.zero_rpow_of_pos h0]
        · exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (GlobalTheory.SplitWeil.Model.nabs_le_one _ hdet)) hs0
      · simp [Set.indicator_of_notMem hX]
    have hint : intM k (Fin n) (Fin n) = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (𝒪[k] : Set k) : Set (Fin n → Fin n → k)) := by
      ext X; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    have hm : MeasurableSet (intM k (Fin n) (Fin n)) := by
      rw [hint]; exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hOm
    calc _ ≤ ∫⁻ X, (intM k (Fin n) (Fin n)).indicator 1 X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono hb
      _ = volM μ (Fin n) (Fin n) (intM k (Fin n) (Fin n)) := lintegral_indicator_one hm
      _ < ⊤ := by
        rw [hint, volM]; erw [Measure.pi_pi]
        simp only [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ => ENNReal.prod_lt_top fun _ _ => hO.lt_top
  · set K : ℝ≥0∞ := ∫⁻ x, (𝒪[k] : Set k).indicator P x ∂μ + μ (𝒪[k] : Set k) with hK
    have hKt : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(GlobalTheory.T.lintegral_abs_pow_integers_finite k μ s hs).ne, hO⟩
    induction n with
    | zero =>
      calc _ ≤ ∫⁻ X, 1 ∂(volM μ (Fin 0) (Fin 0)) := lintegral_mono fun X => ?_
        _ < ⊤ := by rw [lintegral_one, volM]; erw [Measure.pi_univ]; simp
      by_cases hX : X ∈ intM k (Fin 0) (Fin 0)
      · rw [Set.indicator_of_mem hX]
        simp [P, GlobalTheory.SplitWeil.Model.nabs_one]
      · simp [Set.indicator_of_notMem hX]
    | succ n ih =>
      let U : Set (Fin n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
      have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => hOm
      have hUv : (Measure.pi fun _ : Fin n => μ) U = μ 𝒪[k] ^ n := by simp [U, Measure.pi_pi]
      have hUt : μ 𝒪[k] ^ n ≠ ⊤ := ENNReal.pow_ne_top hO
      set I := fun M : Matrix (Fin n) (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) M with hI
      have inner : ∀ M v u, ∫⁻ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
          (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) ∂μ ≤
          U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u := by
        intro M v u
        by_cases h : u ∈ U ∧ v ∈ U ∧ M ∈ intM k (Fin n) (Fin n)
        · obtain ⟨hu, hv, hM⟩ := h
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv]
          simp only [I, Set.indicator_of_mem hM]
          have he : ∀ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) =
              (𝒪[k] : Set k).indicator (fun y => P (M.det * y + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det)) x := by
            intro x
            by_cases hx : x ∈ (𝒪[k] : Set k)
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_intM_blk x u v M).2 ⟨hx, fun j => hu j trivial, fun i => hv i trivial, hM⟩), det_blk, mul_comm x]
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((mem_intM_blk x u v M).1 h).1)]
          simp_rw [he]
          refine (GlobalTheory.T.lintegral_affine_abs_pow_bound k μ s hs0 M.det _).trans (le_of_eq ?_)
          rw [mul_comm]
        · rw [show (fun x => (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))) = fun _ => 0 from ?_]
          · simp
          funext x
          refine Set.indicator_of_notMem (fun hx => h ?_) _
          obtain ⟨_, hu, hv, hM⟩ := (mem_intM_blk x u v M).1 hx
          exact ⟨fun j _ => hu j, fun i _ => hv i, hM⟩
      calc _ ≤ _ := GlobalTheory.T.lintegral_matrix_first_row_column k μ n _
        _ ≤ ∫⁻ M, ∫⁻ v, ∫⁻ u, U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u
              ∂(Measure.pi fun _ : Fin n => μ) ∂(Measure.pi fun _ : Fin n => μ) ∂(volM μ (Fin n) (Fin n)) :=
            lintegral_mono fun M => lintegral_mono fun v => lintegral_mono fun u => inner M v u
        _ = ∫⁻ M, K * I M * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) ∂(volM μ (Fin n) (Fin n)) := by
            refine lintegral_congr fun M => ?_
            simp_rw [lintegral_indicator_const hU, hUv]
            rw [lintegral_mul_const' _ _ hUt, lintegral_indicator_const hU, hUv, mul_assoc]
        _ = K * (∫⁻ M, I M ∂(volM μ (Fin n) (Fin n))) * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) := by
            rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hUt hUt), lintegral_const_mul' _ _ hKt]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hKt.lt_top ih) (ENNReal.mul_lt_top hUt.lt_top hUt.lt_top)

end GlobalTheory.GJInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFiniteStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_det_pow_integer_matrices_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  first | exact @GlobalTheory.GJInt.intdet | exact GlobalTheory.GJInt.intdet | (intros; apply GlobalTheory.GJInt.intdet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL GlobalTheory.CompanionTheory.QL.instMeasGL

noncomputable section
namespace GlobalTheory.GJTransfer

theorem integrable_indicator_intM_mul_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ : ℝ), (n : ℝ) - 1 < σ →
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  intro k _ _ _ _ _ _ n σ hσ
  have hint : ∀ (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), -1 < s →
      ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
        (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
    intro μ _ s hs
    exact GlobalTheory.T.lintegral_det_pow_integer_matrices_finite k μ n s hs
  exact integrable_haarVol_of_lintegral n σ (min (σ - n) 0) (min_le_left _ _)
    (hint _ _ (lt_min (by linarith) (by norm_num)))

end GlobalTheory.GJTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGlStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_det_pow_indicator_integer_gl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ : ℝ), (n : ℝ) - 1 < σ →
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  first | exact @GlobalTheory.GJTransfer.integrable_indicator_intM_mul_nabs_rpow | exact GlobalTheory.GJTransfer.integrable_indicator_intM_mul_nabs_rpow | (intros; apply GlobalTheory.GJTransfer.integrable_indicator_intM_mul_nabs_rpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJIntegrable

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL GlobalTheory.CompanionTheory.QL.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {m : ℕ} {K : Set (Matrix (Fin m) (Fin m) k)} (hK : IsCompact K) :
    ∃ c : kˣ, ∀ X ∈ K, ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover
    (fun y : kˣ => {X : Matrix (Fin m) (Fin m) k | ∀ i j, X i j ∈ cball y})
    (fun y => by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (isOpen_cball y).preimage (show Continuous (fun X : Matrix (Fin m) (Fin m) k => X i j) from
          (continuous_apply j).comp (continuous_apply i)))
    (fun X _ => by
      let f : Option (Fin m × Fin m) → k := fun p => match p with
        | none => 1
        | some q => X q.1 q.2
      obtain ⟨p, hp⟩ := Finite.exists_max fun q => valuation k (f q)
      have h1 : valuation k (f p) ≠ 0 := by
        have := hp none
        simp only [f, map_one] at this
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one this)
      have h0 : f p ≠ 0 := fun h => h1 (by rw [h, map_zero])
      exact Set.mem_iUnion.2 ⟨Units.mk0 _ h0, fun i j => by
        show valuation k (X i j) ≤ valuation k (f p)
        exact hp (some (i, j))⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun X hX i j => le_trans (show valuation k (X i j) ≤ _ from hX i j) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun X hX i j => le_trans (show valuation k (X i j) ≤ _ from hX i j) h⟩)
  exact ⟨y, fun X hX i j => hy hX i j⟩

theorem isLocallyConstant_char {ν : kˣ →* ℂˣ} (hν : IsOpen (ν.ker : Set kˣ)) :
    IsLocallyConstant fun x : kˣ => ((ν x : ℂˣ) : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x0 => ?_
  have hn : (fun x => x0⁻¹ * x) ⁻¹' (ν.ker : Set kˣ) ∈ nhds x0 :=
    (hν.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with x hx
  have hx' : ν (x0⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at hx'
  rw [hx']

theorem nabs_pos_unit (x : kˣ) : 0 < nabs k x := NNReal.coe_pos.mpr distribHaarChar_pos

theorem nabs_pow (x : kˣ) (m : ℕ) : nabs k (x ^ m) = nabs k x ^ m := by
  induction m with
  | zero => simp [nabs]
  | succ m ih => rw [pow_succ, nabs_mul, ih, pow_succ]

theorem integrable_gjIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (haarVol (KO k (Fin n))) := by
  intro k _ _ _ _ _ _ n ν z hν hz φ hφ
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  obtain ⟨hl, hK⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  obtain ⟨C, hC⟩ := hl.continuous.bounded_above_of_compact_support hK
  obtain ⟨c, hc⟩ := exists_unit_bound (k := k) hK.isCompact
  set s : GL (Fin n) k := Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom c⁻¹ with hs
  have hsv : ∀ g : GL (Fin n) k, (s * g).val = ((c⁻¹ : kˣ) : k) • g.val := by
    intro g
    simp [hs, Algebra.smul_def]
  have hsd : ∀ g : GL (Fin n) k, gdet g = c ^ n * gdet (s * g) := by
    intro g
    ext
    simp only [gdet, Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, hsv,
      Matrix.det_smul, Fintype.card_fin, ← mul_assoc, ← mul_pow]
    simp
  set T : GL (Fin n) k → ℝ := fun g =>
    (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ z.re with hT
  have hTi : Integrable T (haarVol (KO k (Fin n))) := GlobalTheory.T.integrable_det_pow_indicator_integer_gl k n z.re hz
  have hT0 : ∀ g, 0 ≤ T g := fun g =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Real.rpow_nonneg (nabs_pos_unit _).le _)
  set D : ℝ := |C| * (nabs k c ^ n) ^ z.re with hD
  have hcont : Continuous fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z := by
    refine ((hl.continuous.comp Units.continuous_val).mul
      ((isLocallyConstant_char hν.1).continuous.comp GeneralLinearGroup.continuous_det)).mul ?_
    exact (((isLocallyConstant_nabs k).comp fun r : ℝ => (r : ℂ) ^ z).continuous).comp
      GeneralLinearGroup.continuous_det
  refine ((hTi.comp_mul_left s).const_mul D).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos_unit (gdet g)
  have hu : ‖((ν (gdet g) : ℂˣ) : ℂ)‖ = 1 := hν.2 _
  rw [norm_mul, norm_mul, hu, mul_one, apow, Complex.norm_cpow_eq_rpow_re_of_pos hp]
  by_cases h0 : φ g.val = 0
  · rw [h0, norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (pow_nonneg (nabs_pos_unit c).le _) _)) (hT0 _)
  have hmem : (s * g).val ∈ intM k (Fin n) (Fin n) := by
    intro i j
    rw [hsv, Matrix.smul_apply, smul_eq_mul, Valuation.mem_integer_iff, map_mul]
    have h1 := hc g.val (subset_tsupport _ h0) i j
    have h2 : valuation k ((c⁻¹ : kˣ) : k) * valuation k (c : k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc valuation k ((c⁻¹ : kˣ) : k) * valuation k (g.val i j)
        ≤ valuation k ((c⁻¹ : kˣ) : k) * valuation k (c : k) := by gcongr
      _ = 1 := h2
  have hTs : T (s * g) = nabs k (gdet (s * g)) ^ z.re := by
    simp only [hT, Set.indicator_of_mem hmem, one_mul]
  show _ ≤ D * T (s * g)
  rw [hTs, hsd g, nabs_mul, nabs_pow, Real.mul_rpow (pow_nonneg (nabs_pos_unit c).le _) (nabs_pos_unit _).le, hD]
  have hq := Real.rpow_nonneg (pow_nonneg (nabs_pos_unit c).le n) z.re
  have hr := Real.rpow_nonneg (nabs_pos_unit (gdet (s * g))).le z.re
  calc ‖φ g.val‖ * ((nabs k c ^ n) ^ z.re * nabs k (gdet (s * g)) ^ z.re)
      ≤ |C| * ((nabs k c ^ n) ^ z.re * nabs k (gdet (s * g)) ^ z.re) :=
        mul_le_mul_of_nonneg_right ((hC _).trans (le_abs_self C)) (mul_nonneg hq hr)
    _ = _ := by ring

end GlobalTheory.GJIntegrable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartzStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_zeta_integral_matrix_schwartz : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (haarVol (KO k (Fin n))) := by
  first | exact @GlobalTheory.GJIntegrable.integrable_gjIntegrand | exact GlobalTheory.GJIntegrable.integrable_gjIntegrand | (intros; apply GlobalTheory.GJIntegrable.integrable_gjIntegrand <;> assumption)
end
