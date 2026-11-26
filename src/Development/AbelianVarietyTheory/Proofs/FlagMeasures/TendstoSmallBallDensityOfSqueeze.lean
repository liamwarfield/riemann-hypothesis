module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueeze
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueeze
open Filter Topology Set

namespace GlobalTheory.IwConst

theorem tendsto_scale_div_pow (b : ℝ → ENNReal) (d : ℕ) (v : ENNReal) (s : ℝ) (hs : 0 < s)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (hv : v ≠ ⊤) :
    Tendsto (fun r : ℝ => ENNReal.ofReal c * b (s * r) / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (c * s ^ d) * v)) := by
  have hs' : Tendsto (fun r : ℝ => s * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun r : ℝ => s * r) (𝓝 (0 : ℝ)) (𝓝 (s * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hs hr
  have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (s ^ d)) (hb.comp hs')
    (Or.inr ENNReal.ofReal_ne_top)
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) h1 (Or.inr ENNReal.ofReal_ne_top)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hsd : ENNReal.ofReal (s ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hs d
  simp only [Function.comp]
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hs.le d), ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ hsd ENNReal.ofReal_ne_top, mul_div_assoc]

theorem tendsto_ofReal_mul_of_one (g : ℝ → ℝ) (v : ENNReal) (hv : v ≠ ⊤)
    (hg : ContinuousAt g 0) (h0 : g 0 = 1) :
    Tendsto (fun η : ℝ => ENNReal.ofReal (g η) * v) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal (g η)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (ENNReal.continuous_ofReal.tendsto (g 0)).comp hg.tendsto
    rw [h0, ENNReal.ofReal_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := ENNReal.Tendsto.mul_const (b := v) h1 (Or.inr hv)
  rw [one_mul] at h2
  exact h2

theorem tendsto_div_pow_of_squeeze (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal) (hv : v ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal,
      Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧
        f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) :
    Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hg : ContinuousAt (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 := by
      fun_prop (disch := norm_num)
    have hg0 : (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 = 1 := by simp
    have hT := tendsto_ofReal_mul_of_one _ v hv hg hg0
    obtain ⟨η, hη, hηpos⟩ := ((tendsto_order.1 hT).1 a ha |>.and self_mem_nhdsWithin).exists
    have hη0 : (0 : ℝ) < η := hηpos
    have h1η : (0 : ℝ) < 1 + η := by linarith
    obtain ⟨b, hb, hev⟩ := h η hη0
    have hL := tendsto_scale_div_pow b d v ((1 + η)⁻¹) (inv_pos.2 h1η) ((1 + η)⁻¹)
      (inv_nonneg.2 h1η.le) hb hv
    filter_upwards [(tendsto_order.1 hL).1 a hη, hev] with r hr1 hr2
    refine lt_of_lt_of_le hr1 (ENNReal.div_le_div_right ?_ _)
    calc ENNReal.ofReal ((1 + η)⁻¹) * b ((1 + η)⁻¹ * r)
        ≤ ENNReal.ofReal ((1 + η)⁻¹) * (ENNReal.ofReal (1 + η) * f r) := by
          gcongr
          rw [← div_eq_inv_mul]
          exact hr2.1
      _ = f r := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 h1η.le), inv_mul_cancel₀ h1η.ne',
            ENNReal.ofReal_one, one_mul]
  · have hg : ContinuousAt (fun η : ℝ => (1 + η) * (1 + η) ^ d) 0 := by fun_prop
    have hg0 : (fun η : ℝ => (1 + η) * (1 + η) ^ d) 0 = 1 := by simp
    have hT := tendsto_ofReal_mul_of_one _ v hv hg hg0
    obtain ⟨η, hη, hηpos⟩ := ((tendsto_order.1 hT).2 a ha |>.and self_mem_nhdsWithin).exists
    have hη0 : (0 : ℝ) < η := hηpos
    obtain ⟨b, hb, hev⟩ := h η hη0
    have hU := tendsto_scale_div_pow b d v (1 + η) (by linarith) (1 + η) (by linarith) hb hv
    filter_upwards [(tendsto_order.1 hU).2 a hη, hev] with r hr1 hr2
    exact lt_of_le_of_lt (ENNReal.div_le_div_right hr2.2 _) hr1

end GlobalTheory.IwConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueezeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_small_ball_density_of_squeeze : ∀ (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal), v ≠ ⊤ → (∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal, Filter.Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) ∧ ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧ f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) → Filter.Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) := by
  first | exact @GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | exact GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | (intros; apply GlobalTheory.IwConst.tendsto_div_pow_of_squeeze <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnfoldKernel
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.AdelicUnfold

theorem unfold_smul {Γ X : Type} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X]
    [MeasurableConstSMul Γ X] (μ : Measure X) [SMulInvariantMeasure Γ X μ] {s : Set X}
    (hs : IsFundamentalDomain Γ s μ) (f : X → ℂ) (hf : Integrable f μ) :
    IntegrableOn (fun z => ∑' γ : Γ, f (γ • z)) s μ ∧
      ∫ z, f z ∂μ = ∫ z in s, ∑' γ : Γ, f (γ • z) ∂μ := by
  classical
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun z => f (γ • z)) μ := fun γ =>
    hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul γ μ)
  have hfin : ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ ≠ ⊤ := by
    rw [← hs.lintegral_eq_tsum'' (fun z => ‖f z‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have hae : ∀ᵐ z ∂μ.restrict s, ∑' γ : Γ, ‖f (γ • z)‖ₑ < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).restrict.enorm)
    rw [lintegral_tsum fun γ => (hmeas γ).restrict.enorm]
    exact hfin
  have hsm : ∀ᵐ z ∂μ.restrict s, Summable fun γ : Γ => f (γ • z) := by
    filter_upwards [hae] with z hz
    exact Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.1 hz.ne)
  have hasm : AEStronglyMeasurable (fun z => ∑' γ : Γ, f (γ • z)) (μ.restrict s) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset Γ)))
      (f := fun t z => ∑ γ ∈ t, f (γ • z)) (fun t => ?_) ?_
    · convert Finset.aestronglyMeasurable_sum t (fun γ _ => (hmeas γ).restrict) using 1
      ext z
      simp [Finset.sum_apply]
    · filter_upwards [hsm] with z hz using hz.hasSum
  refine ⟨⟨hasm, ?_⟩, ?_⟩
  · calc ∫⁻ z in s, ‖∑' γ : Γ, f (γ • z)‖ₑ ∂μ ≤ ∫⁻ z in s, ∑' γ : Γ, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_mono fun z => enorm_tsum_le_tsum_enorm
      _ = ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_tsum fun γ => (hmeas γ).restrict.enorm
      _ < ⊤ := hfin.lt_top
  · rw [integral_tsum (fun γ => (hmeas γ).restrict) hfin]
    exact hs.integral_eq_tsum'' f hf

theorem measurePreserving_left (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (g : I.GA) : MeasurePreserving (fun z => g * z) (I.muA μf) (I.muA μf) := by
  unfold AutInst.muA
  have h0 : ∀ v, (muG (I.ε v)).IsMulLeftInvariant := fun v => inferInstance
  have h1 : (Measure.pi fun v => muG (I.ε v)).IsMulLeftInvariant := inferInstance
  have h2 : ((Measure.pi fun v => muG (I.ε v)).prod μf).IsMulLeftInvariant := inferInstance
  exact measurePreserving_mul_left _ g

theorem integral_unfold_kernel : ∀ (B : RowsAut) (φ F : B.I.GA → ℂ) (x : B.I.GA), (∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, F (γ * z) = F z) → Integrable (fun g => φ g * F (x * g)) (B.I.muA B.μf) → IntegrableOn (fun z => kern B.I φ x z * F z) B.fund (B.I.muA B.μf) ∧ ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z in B.fund, kern B.I φ x z * F z ∂(B.I.muA B.μf) := by
  intro B φ F x hF hint
  have := B.haar
  have := B.sf
  have hcount : Countable (GlobalTheory.RatDiscrete.ratSub B.I) := by
    have := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    exact this
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA :=
    ⟨fun γ => (measurePreserving_left B.I B.μf γ.1).measurable⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun γ A hA => (measurePreserving_left B.I B.μf γ.1).measure_preimage hA.nullMeasurableSet⟩
  have hfd : IsFundamentalDomain (GlobalTheory.RatDiscrete.ratSub B.I) B.fund (B.I.muA B.μf) :=
    GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec

  have hh : Integrable (fun z => φ (x⁻¹ * z) * F z) (B.I.muA B.μf) := by
    have := ((measurePreserving_left B.I B.μf x⁻¹).integrable_comp hint.aestronglyMeasurable).2 hint
    convert this using 1
    ext z
    simp [Function.comp, mul_inv_cancel_left]
  have hB : ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z, φ (x⁻¹ * z) * F z ∂(B.I.muA B.μf) := by
    have hmp := measurePreserving_left B.I B.μf x
    have e := integral_map hmp.measurable.aemeasurable
      (f := fun z => φ (x⁻¹ * z) * F z) (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
    rw [hmp.map_eq] at e
    rw [e]
    congr 1
    ext g
    simp [inv_mul_cancel_left]

  have hD : (fun z => ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I, φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z))
      =ᵐ[(B.I.muA B.μf).restrict B.fund] fun z => kern B.I φ x z * F z := by
    filter_upwards [ae_restrict_of_ae (s := B.fund) hF] with z hz
    unfold kern
    have hγ : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z) = φ (x⁻¹ * γ.1 * z) * F z := fun γ => by
      rw [hz γ.1 γ.2, mul_assoc]
    rw [tsum_congr hγ, tsum_mul_right]
    rfl
  obtain ⟨hI, hE⟩ := unfold_smul (B.I.muA B.μf) hfd (fun z => φ (x⁻¹ * z) * F z) hh
  refine ⟨hI.congr hD, ?_⟩
  rw [hB, hE]
  exact integral_congr_ae hD

end GlobalTheory.AdelicUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidt
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidt
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstApprox

variable {n : ℕ}

theorem nrm_conj_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by

  have hs : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
  unfold nrm
  congr 1
  unfold Formalism.REAL.hs Formalism.REAL.Jm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, hs, hs, one_mul, mul_one]

theorem nrm_sub_proj_le_sq (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (h : IsCut ε S E) (g : Formalism.REAL.UJ ε) (hg : g ∈ S) :
    nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by

  have hON : IsON E := h.isON
  obtain ⟨H, hH, -⟩ := h.subgroup
  obtain ⟨A, hAmul, -, hspan, hS⟩ := h
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hgU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g⁻¹ * uMat g = 1 := by
    show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have h2 : uMat g * uMat g⁻¹ = 1 := by
    show _ * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hinv : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * uMat g⁻¹ := by rw [hJJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by rw [hgU]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h2, Matrix.mul_one]
  have hgH : g ∈ H := by rw [← SetLike.mem_coe, hH]; exact hg
  have hgi : g⁻¹ ∈ S := by rw [← hH]; exact H.inv_mem hgH
  rw [hS] at hg hgi
  have hXA : uMat g - 1 ∈ A := hg
  have hXsA : uMat g⁻¹ - 1 ∈ A := hgi
  have hXs : Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε = uMat g⁻¹ - 1 := by
    rw [hinv]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hJJ]
  have key : (uMat g⁻¹ - 1) * (uMat g - 1) = -((uMat g - 1) + (uMat g⁻¹ - 1)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.mul_one, Matrix.one_mul]
    abel
  have hG : Formalism.REAL.inG ε ((1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := by
    rw [← hXs]
    generalize uMat g - 1 = X
    have h0 : (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε +
        Formalism.REAL.Jm ε * (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) = 0 := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hJt, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, hJJ', Matrix.mul_one]
      abel
    unfold Formalism.REAL.inG
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0,
      smul_zero]
  have hY : (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1)) ∈ Submodule.span ℝ (Set.range E) :=
    (hspan _).1 ⟨A.smul_mem _ (A.sub_mem hXA hXsA), hG⟩
  have hsq : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
    rw [← hXs, nrm_conj_Jm, nrm_conjTranspose]
  calc nrm (uMat g - 1 - cmb E (crd E (uMat g - 1)))
      ≤ nrm (uMat g - 1 - (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := nrm_sub_proj_le hON _ hY
    _ = nrm ((-(1 / 2 : ℝ)) • ((uMat g⁻¹ - 1) * (uMat g - 1))) := by
        rw [key]
        congr 1
        module
    _ = 1 / 2 * nrm ((uMat g⁻¹ - 1) * (uMat g - 1)) := by
        rw [nrm_smul]
        norm_num
    _ ≤ 1 / 2 * (nrm (uMat g⁻¹ - 1) * nrm (uMat g - 1)) := by
        gcongr
        exact nrm_mul_le _ _
    _ ≤ nrm (uMat g - 1) ^ 2 := by
        rw [hsq]
        nlinarith [sq_nonneg (nrm (uMat g - 1)), nrm_nonneg (uMat g - 1)]

end GlobalTheory.IwConstApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidtStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ g ∈ S, nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by
  first | exact @GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | exact GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | (intros; apply GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Imports
namespace GlobalTheory.TargetStatementBis

open NumberField

theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V)
    (h : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h₁⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero b.2), ?_⟩
    have key : ((b : 𝓞 K)) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : 𝓞 K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, key, smul_comm d a x]
    exact Λ.smul_mem a h₁

theorem target : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V] (Λ : Submodule (NumberField.RingOfIntegers K) V), Submodule.span K (↑Λ : Set V) = ⊤ → ∀ (v : V), ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ Λ :=
  fun Λ h v => main Λ h v

end GlobalTheory.TargetStatementBis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubtype
namespace GlobalTheory.SmulMemComapLattice

open NumberField

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (v : V) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hax
    · rw [mul_smul]; exact L.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap R K q ≠ 0 := by
      simpa using hq0
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have : (q * a) • (algebraMap R K p / algebraMap R K q) • x = p • a • x := by
      rw [← algebraMap_smul K (q * a), ← algebraMap_smul K p, ← algebraMap_smul K a x,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ hax

theorem isLattice_comap_subtype {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsFullLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Submodule.comap (LinearMap.restrictScalars (𝓞 K) W.subtype) Λ) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (LinearMap.restrictScalars (𝓞 K) W.subtype) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.SmulMemComapLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegers
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_ne_zero_smul_mem_of_span_eq_top {K V : Type} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.TargetStatementBis.target
  | exact _root_.GlobalTheory.TargetStatementBis.target
  | (apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementBis.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementBis.target ..)

theorem isLattice_comap_subtype_ringOfIntegers {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (W.subtype.restrictScalars (𝓞 K)) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegersStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V), Submodule.IsLattice K Λ → ∀ W : Submodule K V, Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.isLattice_comap_subtype_ringOfIntegers | exact GlobalTheory.isLattice_comap_subtype_ringOfIntegers | (intros; apply GlobalTheory.isLattice_comap_subtype_ringOfIntegers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompact
open MeasureTheory Filter Set Formalism.MainNotions.S GlobalTheory.RightRegFund
open scoped ENNReal Pointwise

namespace GlobalTheory.LocalL2Isometry

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ]
  {D : Set G} {r : G → G}

private lemma card_le_of_translates_mem_mul_inv_tsum_indicator {C : Set G} (S : Finset Γ)
    (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) (x : G) :
    ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ S.card := by
  classical
  by_cases h : ∃ γ₀ : Γ, (γ₀ : G) * x ∈ C
  · obtain ⟨γ₀, h₀⟩ := h
    have hsupp : ∀ γ ∉ S.image (· * γ₀),
        C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) = 0 := by
      intro γ hγ
      by_contra hne
      have hγC : (γ : G) * x ∈ C := by
        by_contra hn
        exact hne (Set.indicator_of_notMem hn _)
      apply hγ
      refine Finset.mem_image.2 ⟨γ * γ₀⁻¹, hS _ ?_, by simp⟩
      refine Set.mem_mul.2 ⟨(γ : G) * x, hγC, ((γ₀ : G) * x)⁻¹, by simpa using h₀, ?_⟩
      simp [mul_assoc]
    rw [tsum_eq_sum hsupp]
    calc ∑ γ ∈ S.image (· * γ₀), C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)
        ≤ ∑ _γ ∈ S.image (· * γ₀), (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun γ _ => ?_
          by_cases hm : (γ : G) * x ∈ C <;> simp [hm]
      _ = ((S.image (· * γ₀)).card : ℝ≥0∞) := by simp
      _ ≤ S.card := by exact_mod_cast Finset.card_image_le
  · push_neg at h
    simp [h]

theorem lintegral_rep_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y in C, φ (r y) ∂μ ≤ S.card * ∫⁻ x in D, φ x ∂μ := by
  classical
  have hfix : ∀ᵐ x ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * x) = x := by
    filter_upwards [ae_restrict_of_ae (ae_good hD), ae_restrict_mem hDm] with x hx hxD γ
    rw [rep_mul hr hx γ]
    simpa using rep_eq hr hx (γ := 1) (by simpa using hxD)
  have hmeas : ∀ γ : Γ, AEMeasurable
      (fun x => C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x) (μ.restrict D) := fun γ =>
    (((measurable_const.indicator hC).comp (measurable_const_mul (γ : G))).mul hφ).aemeasurable
  calc ∫⁻ y in C, φ (r y) ∂μ = ∫⁻ y, C.indicator (fun y => φ (r y)) y ∂μ :=
        (lintegral_indicator hC _).symm
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun y => φ (r y)) (γ • x) ∂μ :=
        hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ := by
        refine tsum_congr fun γ => lintegral_congr_ae ?_
        filter_upwards [hfix] with x hx
        change C.indicator (fun y => φ (r y)) ((γ : G) * x) = _
        by_cases hm : (γ : G) * x ∈ C
        · simp [hm, hx γ]
        · simp [hm]
    _ = ∫⁻ x in D, ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ :=
        (lintegral_tsum hmeas).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) * φ x ∂μ :=
        lintegral_congr fun x => ENNReal.tsum_mul_right
    _ ≤ ∫⁻ x in D, (S.card : ℝ≥0∞) * φ x ∂μ :=
        lintegral_mono fun x => by gcongr; exact card_le_of_translates_mem_mul_inv_tsum_indicator S hS x
    _ = S.card * ∫⁻ x in D, φ x ∂μ := lintegral_const_mul _ hφ

theorem integrableOn_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (hCf : μ C ≠ ∞) (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) :
    ∃ M : ℝ, ∀ F : Lp ℂ 2 (μ.restrict D), IntegrableOn (fun y => F (r y)) C μ ∧
      ∫ y in C, ‖F (r y)‖ ∂μ ≤ M * ‖F‖ := by
  refine ⟨((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal, fun F => ?_⟩
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hCf
  have hFm : Measurable (F : G → ℂ) := (Lp.stronglyMeasurable F).measurable
  have hgm : AEStronglyMeasurable (fun y => F (r y)) (μ.restrict C) :=
    (aestronglyMeasurable_comp_rep hD hDm hr (Lp.stronglyMeasurable F)).restrict
  have hcard : (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.natCast_ne_top _)
  have hCr : μ C ^ (1 / 2 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCf
  have h2 : eLpNorm (fun y => F (r y)) 2 (μ.restrict C) ≤
      (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hgm,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
        (Lp.stronglyMeasurable F).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    gcongr
    exact lintegral_rep_le hD hDm hr hC S hS (φ := fun x => ‖F x‖ₑ ^ (2 : ℝ)) (by fun_prop)
  have h1 : eLpNorm (fun y => F (r y)) 1 (μ.restrict C) ≤
      eLpNorm (fun y => F (r y)) 2 (μ.restrict C) * μ C ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hgm
    rw [Measure.restrict_apply_univ] at h
    convert h using 3
    norm_num
  have hL2 : MemLp (fun y => F (r y)) 2 (μ.restrict C) :=
    h2.trans_lt (ENNReal.mul_lt_top hcard.lt_top (Lp.eLpNorm_lt_top F))
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  calc ∫ y in C, ‖F (r y)‖ ∂μ = (eLpNorm (fun y => F (r y)) 1 (μ.restrict C)).toReal := by
        rw [integral_norm_eq_lintegral_enorm hgm, eLpNorm_one_eq_lintegral_enorm hgm]
    _ ≤ ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) * μ C ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hcard (Lp.eLpNorm_ne_top F)) hCr)
          (h1.trans (by gcongr))
    _ = ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal * ‖F‖ := by
        rw [Lp.norm_def, ← ENNReal.toReal_mul, mul_right_comm]

theorem ext_integrableOn : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ,
    ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧
      ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  intro B C hC
  obtain ⟨Γ, hΓ, hΓc, hfin, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain B.I
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology B.I
  haveI := hΓc
  haveI := hT2
  haveI := hsc
  have hD := hfd B.μf B.fund B.fund_spec
  haveI : (B.I.muA B.μf).IsMulLeftInvariant := ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).1⟩
  haveI : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  have hDm : MeasurableSet B.fund := B.fund_spec.1
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have h := B.fund_spec.2.1 y
    refine ⟨⟨h.choose, ?_⟩, ?_, ?_⟩
    · rw [← SetLike.mem_coe, hΓ]
      exact h.choose_spec.1
    · rw [AutInst.rep, dite_eq_left h]
    · rw [AutInst.rep, dite_eq_left h]
      exact h.choose_spec.2
  have hK : IsCompact (C * C⁻¹) := hC.mul hC.inv
  have hSfin : {γ : Γ | (γ : B.I.GA) ∈ C * C⁻¹}.Finite :=
    ((hfin _ hK).preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨hγ, by
      rw [← hΓ]
      exact γ.2⟩
  obtain ⟨M, hM⟩ := integrableOn_rep hD hDm hr hC.measurableSet hC.measure_lt_top.ne
    hSfin.toFinset fun γ hγ => hSfin.mem_toFinset.2 hγ
  exact ⟨M, fun F => hM F⟩

end GlobalTheory.LocalL2Isometry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompactStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantExtension_integrableOn_compact : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ, ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧ ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.LocalL2Isometry.ext_integrableOn | exact GlobalTheory.LocalL2Isometry.ext_integrableOn | (intros; apply GlobalTheory.LocalL2Isometry.ext_integrableOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLatti
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabFin

section Core

variable {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]

theorem finite_of_fix (hT : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V)
    (hpos : ∀ x ∈ (⨅ u ∈ U, LinearMap.ker (hT u)), x ≠ 0 → 0 < Algebra.trace ℚ E (hT x x))
    (Λ₀ : Submodule (𝓞 E) V) (hΛ : Submodule.IsFullLattice E Λ₀) :
    {h : V ≃ₗ[E] V | h ∈ Formalism.HermitianLatticesTheory.isom hT ∧ (∀ u ∈ U, h u = u) ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  set W : Submodule E V := ⨅ u ∈ U, LinearMap.ker (hT u) with hWdef
  have memW : ∀ y, y ∈ W ↔ ∀ x ∈ U, hT x y = 0 := fun y => by
    simp [hWdef, Submodule.mem_iInf]
  have hdisj : U ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxW⟩
    by_contra hx0
    have := hpos x hxW hx0
    rw [(memW x).1 hxW x hxU] at this
    simp at this
  have hsup : U ⊔ W = ⊤ := by
    let b := Module.finBasis E U
    let φ : V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => hT (b i : V)
    have hker : LinearMap.ker φ ≤ W := by
      intro y hy
      rw [memW]
      intro x hx
      have hy' : ∀ i, hT (b i : V) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy' i, smul_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      refine (Submodule.finrank_le _).trans ?_
      simp
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hdisj, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    have h5 := Submodule.finrank_le (U ⊔ W)
    omega
  have hmul : ∀ v : V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ₀ := fun v => by
    have hv : v ∈ Submodule.span E (Λ₀ : Set V) := by rw [Submodule.IsFullLattice.span_eq_top (self := hΛ)]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  let L : Submodule (𝓞 E) W := Λ₀.comap (W.subtype.restrictScalars (𝓞 E))
  have hfg : L.FG := by
    apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars (𝓞 E)) Subtype.val_injective
    exact hΛ.fg.of_le (Submodule.map_comap_le _ _)
  haveI : Submodule.IsLattice E L := Submodule.IsLattice.of_fg E hfg
  let hW := hT.domRestrict₁₂ W W
  have hposW : ∀ w : W, w ≠ 0 → 0 < Algebra.trace ℚ E (hW w w) := fun w hw =>
    hpos w w.2 fun h0 => hw (Subtype.ext h0)
  obtain ⟨N, hN⟩ := hfg
  have hNL : ∀ n ∈ N, ((n : W) : V) ∈ Λ₀ := fun n hn => by
    have : n ∈ L := hN ▸ Submodule.subset_span hn
    exact this
  have hpres : ∀ h : V ≃ₗ[E] V, h ∈ Formalism.HermitianLatticesTheory.isom hT → (∀ u ∈ U, h u = u) → ∀ w ∈ W, h w ∈ W := by
    intro h hiso hfix w hw
    rw [memW] at hw ⊢
    intro x hx
    rw [← hfix x hx, hiso x w]
    exact hw x hx
  refine Set.Finite.of_finite_image (f := fun (h : V ≃ₗ[E] V) (n : N) => h ((n : W) : V)) ?_ ?_
  · refine (Set.Finite.pi (t := fun n : N => Subtype.val '' {v : W | v ∈ L ∧
        Algebra.trace ℚ E (hW v v) ≤ Algebra.trace ℚ E (hW (n : W) (n : W))})
      fun n => (Formalism.HermitianLatticesTheory.autFinite_short hW hposW L _).image _).subset ?_
    rintro _ ⟨h, ⟨hiso, hfix, hlat⟩, rfl⟩ n _
    refine ⟨⟨h ((n : W) : V), hpres h hiso hfix _ (n : W).2⟩, ⟨?_, ?_⟩, rfl⟩
    · have hm : ((h : V →ₗ[E] V).restrictScalars (𝓞 E)) ((n : W) : V) ∈ Formalism.HermitianLatticesTheory.gmap h Λ₀ :=
        Submodule.mem_map_of_mem (hNL n n.2)
      rw [hlat] at hm
      exact hm
    · show Algebra.trace ℚ E (hT (h ((n : W) : V)) (h ((n : W) : V))) ≤
        Algebra.trace ℚ E (hT ((n : W) : V) ((n : W) : V))
      rw [hiso]
  · rintro h₁ ⟨-, hf1, -⟩ h₂ ⟨-, hf2, -⟩ heq
    let K : Submodule E V := LinearMap.ker ((h₁ : V →ₗ[E] V) - (h₂ : V →ₗ[E] V))
    have memK : ∀ x, x ∈ K ↔ h₁ x = h₂ x := fun x => by
      simp [K, LinearMap.mem_ker, sub_eq_zero]
    have hLK : L ≤ (K.restrictScalars (𝓞 E)).comap (W.subtype.restrictScalars (𝓞 E)) := by
      rw [← hN]
      refine Submodule.span_le.2 fun n hn => ?_
      show ((n : W) : V) ∈ K
      rw [memK]
      exact congrFun heq ⟨n, hn⟩
    have hWK : W ≤ K := by
      intro w hw
      obtain ⟨d, hd0, hd⟩ := hmul w
      have h1 : (⟨d • w, W.smul_of_tower_mem d hw⟩ : W) ∈ L := hd
      have h2 : d • w ∈ K := hLK h1
      rw [← algebraMap_smul E d w] at h2
      exact (Submodule.smul_mem_iff K
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h2
    have hUK : U ≤ K := fun u hu => by rw [memK, hf1 u hu, hf2 u hu]
    have htop : ⊤ ≤ K := hsup ▸ sup_le hUK hWK
    exact LinearEquiv.ext fun x => (memK x).1 (htop trivial)

end Core

theorem stab_finite : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  intro D T T' F F' hpos Λ₀ hΛ
  refine (finite_of_fix (VS D).hT (Xplus F ⊔ Xplus F') hpos Λ₀ hΛ).subset ?_
  rintro h ⟨⟨hiso, hF, hF'⟩, hlat⟩
  refine ⟨hiso, ?_, hlat⟩
  have key : ∀ {T0 : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T0), (∀ a, h (frame G a) = frame G a) →
      Xplus G ≤ LinearMap.ker ((h : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
    intro T0 G hG
    have he : ∀ i, h (G.fl.e i) = G.fl.e i := fun i => by
      have := hG (Fin.castSucc i)
      simpa [frame, FlagG.fvec] using this
    have hz : h G.fl.z = G.fl.z := by
      have := hG (Fin.last _)
      simpa [frame, FlagG.fvec] using this
    show Submodule.span D.host.E (Set.range G.fl.e) ⊔ Submodule.span D.host.E {G.fl.z} ≤ _
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      simp [he i]
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp [hz]
  intro u hu
  have := (sup_le (key F hF) (key F' hF')) hu
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.StabFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLattiStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_isometriesFixingBothFrames_stabilizing_lattice : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  first | exact @GlobalTheory.StabFin.stab_finite | exact GlobalTheory.StabFin.stab_finite | (intros; apply GlobalTheory.StabFin.stab_finite <;> assumption)
end
end
