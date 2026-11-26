module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselInnerIntegralEqForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselInnerIntegralEqForm
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.InnerInt

theorem hpk_det_isUnit (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem gg_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.1 a ha b hb

theorem gg_inv {k r : ℕ} {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det ∧ a⁻¹ ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.2 a ha

theorem inner_map_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (u v : H) : ⟪T u, T v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (⟨T.toLinearMap, fun v => hT v⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v

theorem star_coef_mul_eq {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) (w : H) {y s x : Mat k r}
    (hy : y ∈ GG k r) (hs : s ∈ GG k r) (hx : x ∈ GG k r) :
    star (coef σ w w (y⁻¹ * (s * x))) = coef σ (σ y w) (σ x w) s⁻¹ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  obtain ⟨hyu, hyi⟩ := gg_inv hy
  obtain ⟨hsu, hsi⟩ := gg_inv hs
  have e1 : σ (y⁻¹ * (s * x)) = (σ y⁻¹).comp ((σ s).comp (σ x)) := by
    rw [hmul _ hyi _ (gg_mul hs hx), hmul _ hs _ hx]
  have e2 : ∀ v, σ y (σ y⁻¹ v) = v := by
    intro v
    have h := hmul _ hy _ hyi
    rw [Matrix.mul_nonsing_inv _ hyu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  have e3 : ∀ v, σ s⁻¹ (σ s v) = v := by
    intro v
    have h := hmul _ hsi _ hs
    rw [Matrix.nonsing_inv_mul _ hsu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  simp only [coef]
  rw [e1, ← starRingEnd_apply, inner_conj_symm]
  simp only [ContinuousLinearMap.comp_apply]
  have i1 := inner_map_of_norm (σ y) (hiso y hy) (σ y⁻¹ (σ s (σ x w))) w
  rw [e2] at i1
  rw [← i1]
  have i2 := inner_map_of_norm (σ s⁻¹) (hiso _ hsi) (σ s (σ x w)) (σ y w)
  rw [e3] at i2
  rw [← i2]

end GlobalTheory.SgInf.InnerInt


open GlobalTheory.SgInf.InnerInt in
theorem GlobalTheory.SgInf.inner_integral_eq_be : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ W : Mat k r → Wp, IsSPsiEquiv z (psiGen k r z c) π W → ∀ y ∈ GG k r, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ∫ s, star (coef σ w w (y⁻¹ * (Matrix.of s * Matrix.of x))) • W (Matrix.of s * Matrix.of x) ∂μS = be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hstd hside W hW y hy x hx
  have hσ : IsURepOn (GG k r) σ := hstd.2.1
  have hdec : Decay σ (DD σ w : Set H) a := hstd.2.2.2.2.2.2.2.1
  have hz := hside.1
  have hT := hside.2.1
  have hπ := hside.2.2.1
  have hhaar := hside.2.2.2.1
  have hSG : Sset k r z ⊆ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1.1
  have hpis := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have huni := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hhaar
  have hstab : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
    intro g hg v hv
    have hle : Submodule.map (σ g).toLinearMap (DD σ w) ≤ DD σ w := by
      rw [DD, Submodule.map_span_le]
      rintro _ ⟨g', hg', rfl⟩
      have : (σ g).toLinearMap (σ g' w) = σ (g * g') w := by
        rw [hσ.1.2 g hg g' hg']; rfl
      rw [this]; exact mem_DD σ w (gg_mul hg hg')
    exact hle ⟨v, hv, rfl⟩
  have hD := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hstd hside (DD σ w : Set H) hstab hdec
    (σ y w) (mem_DD σ w hy) (σ (Matrix.of x) w) (mem_DD σ w hx)
  have hFi := hD.1
  have hGi := hFi.apply_continuousLinearMap (W (Matrix.of x))
  have hm : AEStronglyMeasurable (fun s : Mt k r => (coef σ (σ y w) (σ (Matrix.of x) w) (Matrix.of s) •
      PiS (psiGen k r z c) π (Matrix.of s)⁻¹) (W (Matrix.of x))) (μS.map invM) := by
    rw [huni.2]; exact hGi.aestronglyMeasurable
  have hmap := integral_map measurable_invM.aemeasurable hm
  rw [huni.2] at hmap
  unfold be
  rw [ContinuousLinearMap.integral_apply hFi, hmap]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := ae_iff.2 hhaar.2.2.1
  filter_upwards [hae] with s hs
  have hsG := hSG hs
  have hdet := (gg_inv hsG).1
  obtain ⟨h, hh, m, hm', hsm⟩ := hs
  rw [of_invM, Matrix.nonsing_inv_nonsing_inv _ hdet, ContinuousLinearMap.smul_apply,
    star_coef_mul_eq σ hσ w hy hsG hx]
  congr 1
  rw [hsm, hW h hh m hm' _ hx, (hpis.1 h hh m hm').2, ContinuousLinearMap.smul_apply]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselInnerIntegralEqFormStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_inner_integral_eq_form : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ W : Mat k r → Wp, IsSPsiEquiv z (psiGen k r z c) π W → ∀ y ∈ GG k r, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ∫ s, star (coef σ w w (y⁻¹ * (Matrix.of s * Matrix.of x))) • W (Matrix.of s * Matrix.of x) ∂μS = be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
  first | exact @GlobalTheory.SgInf.inner_integral_eq_be | exact GlobalTheory.SgInf.inner_integral_eq_be | (intros; apply GlobalTheory.SgInf.inner_integral_eq_be <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariant
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.AbsConv

variable {k r : ℕ}

theorem measurable_lmul : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem lintegral_lt_top {μG μS ν : Measure (Mt k r)} [SFinite μG] [SFinite μS] [SFinite ν]
    {S : Set (Mat k r)} (hq : IsQuotMeas μG μS ν)
    (hmap : μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1))
    (hS : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ S)
    (hR : ∀ s ∈ S, μS.map (rmulM s) = μS)
    {φ : Mt k r → ENNReal} (hφ : Measurable φ)
    (hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤)
    {Wn : Mt k r → ENNReal} (hWG : AEMeasurable Wn μG) (hWν : AEMeasurable Wn ν)
    (hinv : ∀ᵐ x ∂ν, ∀ s ∈ S, Wn (lmulM s x) = Wn x)
    (hl2 : ∫⁻ x, Wn x ^ 2 ∂ν < ⊤) :
    ∫⁻ g, φ g * Wn g ∂μG < ⊤ := by
  have hmeas2 : Measurable (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1)) :=
    hφ.comp GlobalTheory.SgInf.AbsConv.measurable_lmul
  have hsec : ∀ x : Mt k r, Measurable (fun t : Mt k r => φ (lmulM (Matrix.of t : Mat k r) x)) :=
    fun x => hmeas2.comp measurable_prodMk_left
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Mt k r → ENNReal,
      Φ = fun x => ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := ⟨_, rfl⟩
  have hΦx : ∀ x, Φ x = ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := fun x => by rw [hΦdef]
  have hΦm : Measurable Φ := by rw [hΦdef]; exact hmeas2.lintegral_prod_right'

  have hΦinv : ∀ s ∈ S, ∀ x, Φ (lmulM s x) = Φ x := by
    intro s hs x
    have hrm : Measurable (rmulM s : Mt k r → Mt k r) := (continuous_rmulM s).measurable
    rw [hΦx, hΦx]
    conv_rhs => rw [← hR s hs]
    rw [lintegral_map (hsec x) hrm]
    refine lintegral_congr fun t => ?_
    congr 1
    change (Matrix.of t * (s * Matrix.of x) : Mat k r) = Matrix.of t * s * Matrix.of x
    rw [Matrix.mul_assoc]

  have hΦ2 : ∫⁻ x, Φ x * Φ x ∂ν < ⊤ := by
    have hF : Measurable (fun g : Mt k r => φ g * Φ g) := hφ.mul hΦm
    have e1 : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG
        = ∫⁻ g, φ g * Φ g ∂μG := by
      refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul _ (hsec g), hΦx]
    have e2 : ∫⁻ g, φ g * Φ g ∂μG = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) *
        Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν := hq _ hF
    have e3 : ∀ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS
        = Φ x * Φ x := by
      intro x
      rw [lintegral_congr_ae (g := fun s => φ (lmulM (Matrix.of s : Mat k r) x) * Φ x) ?_]
      · rw [lintegral_mul_const _ (hsec x), ← hΦx]
      · filter_upwards [hS] with s hs
        rw [hΦinv _ hs x]
    calc ∫⁻ x, Φ x * Φ x ∂ν
        = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν :=
          lintegral_congr fun x => (e3 x).symm
      _ = ∫⁻ g, φ g * Φ g ∂μG := e2.symm
      _ = _ := e1.symm
      _ < ⊤ := hfin

  have hWmm : Measurable (hWν.mk Wn) := hWν.measurable_mk
  have h1 : ∀ᵐ x ∂ν, (∀ s ∈ S, Wn (lmulM s x) = Wn x) ∧ Wn x = hWν.mk Wn x :=
    hinv.and hWν.ae_eq_mk
  have h1' : ∀ᵐ p ∂(ν.prod μS), (∀ s ∈ S, Wn (lmulM s p.1) = Wn p.1) ∧ Wn p.1 = hWν.mk Wn p.1 :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h2 : ∀ᵐ p ∂(ν.prod μS), (Matrix.of p.2 : Mat k r) ∈ S :=
    Measure.quasiMeasurePreserving_snd.ae hS
  have hA : AEMeasurable (fun g => φ g * Wn g)
      ((ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1)) := by
    rw [← hmap]; exact hφ.aemeasurable.mul hWG
  have hmain : ∫⁻ g, φ g * Wn g ∂μG = ∫⁻ x, Φ x * hWν.mk Wn x ∂ν := by
    rw [hmap, lintegral_map' hA GlobalTheory.SgInf.AbsConv.measurable_lmul.aemeasurable]
    rw [lintegral_congr_ae (g := fun p : Mt k r × Mt k r =>
      φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1) ?_]
    · rw [lintegral_prod (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1)
        (hmeas2.mul (hWmm.comp measurable_fst)).aemeasurable]
      refine lintegral_congr fun x => ?_
      dsimp only
      rw [lintegral_mul_const _ (hsec x), ← hΦx]
    · filter_upwards [h1', h2] with p hp1 hp2
      simp only [hp1.1 _ hp2, hp1.2]

  have hpt : ∀ x, Φ x * hWν.mk Wn x ≤ hWν.mk Wn x ^ 2 + Φ x * Φ x := by
    intro x
    rcases le_total (Φ x) (hWν.mk Wn x) with h | h
    · calc Φ x * hWν.mk Wn x ≤ hWν.mk Wn x * hWν.mk Wn x := by gcongr
        _ = hWν.mk Wn x ^ 2 := (sq _).symm
        _ ≤ _ := le_self_add
    · calc Φ x * hWν.mk Wn x ≤ Φ x * Φ x := by gcongr
        _ ≤ _ := le_add_self
  have hW2 : ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν = ∫⁻ x, Wn x ^ 2 ∂ν :=
    lintegral_congr_ae (hWν.ae_eq_mk.symm.fun_comp (· ^ 2))
  rw [hmain]
  calc ∫⁻ x, Φ x * hWν.mk Wn x ∂ν ≤ ∫⁻ x, hWν.mk Wn x ^ 2 + Φ x * Φ x ∂ν := lintegral_mono hpt
    _ = ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν + ∫⁻ x, Φ x * Φ x ∂ν := lintegral_add_left (hWmm.pow_const 2) _
    _ < ⊤ := by rw [hW2]; exact ENNReal.add_lt_top.2 ⟨hl2, hΦ2⟩

theorem enorm_star' (a : ℂ) : ‖star a‖ₑ = ‖a‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]

theorem coef_inv_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) {y g : Mat k r}
    (hy : y ∈ GG k r) (hyi : y⁻¹ ∈ GG k r) (hg : g ∈ GG k r) :
    coef σ w w (y⁻¹ * g) = coef σ w (σ y w) g := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hyy : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y (isUnit_det_of_mem_GG hy)
  have key : ∀ v : H, σ y (σ y⁻¹ v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) (hmul y hy y⁻¹ hyi)
    simp only [hyy, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have hinner : ∀ u v : H, ⟪σ y u, σ y v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ y).toLinearMap, norm_map' := hiso y hy }
    exact L.inner_map_map u v
  simp only [coef]
  rw [hmul y⁻¹ hyi g hg, ContinuousLinearMap.comp_apply, ← hinner w (σ y⁻¹ (σ g w)), key]

theorem norm_equiv {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    (hπ : IsURepOn (UWset k r z) π) {W : Mat k r → Wp} (hW : IsSPsiEquiv z (psiGen k r z c) π W)
    {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : ‖W (s * x)‖ₑ = ‖W x‖ₑ := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hx' : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hx
  rw [hW h hh m hm x hx']
  obtain ⟨-, hiso, -⟩ := hπ
  have hψ : ‖psiGen k r z c m‖ = 1 := by simp [psiGen, Complex.norm_exp]
  have hn : ‖psiGen k r z c m • π h (W x)‖ = ‖W x‖ := by rw [norm_smul, hψ, one_mul, hiso h hh]
  simp only [enorm_eq_nnnorm]
  congr 1
  exact NNReal.eq hn

theorem integrable_coef_smul : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG := by
  classical
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq W hWG hWν hW hl2 y hy
  have hint := GlobalTheory.T.besselForm_coeff_product_fubini_integrable k r σ w a μG d z c π μS hStd hSide
  obtain ⟨-, hσ, -, -, hHG, -, -, -, -⟩ := hStd
  obtain ⟨hz, hT, hπ, hHS, -⟩ := hSide
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hUS : IsUnimod (Sset k r z) μS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHS
  obtain ⟨hνσ, hνG, hmap, -, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHG hHS hUS hq
  have : SigmaFinite μG := hHG.1
  have : SigmaFinite μS := hHS.1
  have : SigmaFinite ν := hνσ
  have hyi : y⁻¹ ∈ GG k r := hcl.1.2.2.2.2 y hy
  have hone : (1 : Mat k r) ∈ GG k r := hcl.1.2.2.1
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this
  have hyD : σ y w ∈ DD σ w := mem_DD σ w hy
  have hint2 := hint w hwD w hwD (σ y w) hyD (σ y w) hyD

  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GGset : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ GG k r} with hGGdef
  have hGGmeas : MeasurableSet GGset := (hcl.1.2.1.preimage hof).measurableSet
  have hGae : ∀ᵐ x ∂μG, x ∈ GGset := ae_iff.2 hHG.2.2.1
  have hc0 : ContinuousOn (fun g : Mt k r => σ (Matrix.of g) w) GGset :=
    (hσ.2.2 w).comp hof.continuousOn (fun x hx => hx)
  have hcc : ContinuousOn (fun g : Mt k r => coef σ w (σ y w) (Matrix.of g)) GGset := by
    simp only [coef]
    exact continuousOn_const.inner hc0

  obtain ⟨φ, hφdef⟩ : ∃ φ : Mt k r → ENNReal,
      φ = GGset.piecewise (fun g => ‖coef σ w (σ y w) (Matrix.of g)‖ₑ) 0 := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφdef]
    exact ContinuousOn.measurable_piecewise (continuous_enorm.comp_continuousOn hcc)
      continuousOn_const hGGmeas
  have hφle : ∀ g, φ g ≤ ‖coef σ w (σ y w) (Matrix.of g)‖ₑ := by
    intro g
    rw [hφdef]
    by_cases hg : g ∈ GGset
    · simp [Set.piecewise, hg]
    · simp [Set.piecewise, hg]
  have hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤ := by
    have hfi := hint2.hasFiniteIntegral
    unfold HasFiniteIntegral at hfi
    refine lt_of_le_of_lt ?_ hfi
    refine le_trans (lintegral_mono fun g => lintegral_mono fun t => ?_) (lintegral_prod _ hint2.aestronglyMeasurable.enorm).symm.le
    dsimp only
    rw [enorm_mul, GlobalTheory.SgInf.AbsConv.enorm_star']
    exact mul_le_mul' (hφle g) (hφle _)
  have hinv : ∀ᵐ x ∂ν, ∀ s ∈ Sset k r z,
      ‖W (Matrix.of (lmulM s x))‖ₑ = ‖W (Matrix.of x)‖ₑ := by
    have : ∀ᵐ x ∂ν, x ∈ GGset := ae_iff.2 hνG
    filter_upwards [this] with x hx s hs
    exact GlobalTheory.SgInf.AbsConv.norm_equiv hπ hW hs hx
  have hl2' : ∫⁻ x, ‖W (Matrix.of x)‖ₑ ^ 2 ∂ν < ⊤ := by
    simpa only [l2SG, enorm_eq_nnnorm] using hl2
  have hbound := GlobalTheory.SgInf.AbsConv.lintegral_lt_top (S := Sset k r z) hq hmap (ae_iff.2 hHS.2.2.1)
    hUS.1 hφm hfin hWG.enorm hWν.enorm hinv hl2'

  have hcm : AEStronglyMeasurable (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g))) μG := by
    rw [← Measure.restrict_eq_self_of_ae_mem hGae]
    exact hcc.star.aestronglyMeasurable hGGmeas
  have hsm : AEStronglyMeasurable
      (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) μG := hcm.smul hWG
  have hae : (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g))
      =ᵐ[μG] (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) := by
    filter_upwards [hGae] with g hg
    rw [GlobalTheory.SgInf.AbsConv.coef_inv_mul (g := Matrix.of g) hσ w hy hyi hg]
  refine Integrable.congr ⟨hsm, ?_⟩ hae.symm
  show ∫⁻ g, ‖star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)‖ₑ ∂μG < ⊤
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hbound
  filter_upwards [hGae] with g hg
  rw [enorm_smul, GlobalTheory.SgInf.AbsConv.enorm_star', hφdef, Set.piecewise_eq_of_mem _ _ _ hg]

end GlobalTheory.SgInf.AbsConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariantStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_besselCoefficient_smul_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG := by
  first | exact @GlobalTheory.SgInf.AbsConv.integrable_coef_smul | exact GlobalTheory.SgInf.AbsConv.integrable_coef_smul | (intros; apply GlobalTheory.SgInf.AbsConv.integrable_coef_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonality
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonality
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem fdegH_eq_of_schurH (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H)
    (hS : SchurH μG σ d) (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, hrel⟩ := hS
  obtain ⟨-, hint⟩ := hrel w w w w
  have hpt : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g))
      = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    simp only [coef]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpt] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have hreal : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hint]
    push_cast
    rw [← pow_add]
    rfl
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegH
  rw [hreal]
  have h4 : (‖w‖ ^ 4 : ℝ) ≠ 0 := by positivity
  field_simp

end GlobalTheory.SgInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonalityStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H), SchurH μG σ d → w ≠ 0 → fdegH μG σ w = d := by
  first | exact @GlobalTheory.SgInf.fdegH_eq_of_schurH | exact GlobalTheory.SgInf.fdegH_eq_of_schurH | (intros; apply GlobalTheory.SgInf.fdegH_eq_of_schurH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSide
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.KernelRe

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

def lmulEquiv (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := lmulM a x
  invFun x := lmulM a⁻¹ x
  left_inv x := by
    show (a⁻¹ * (a * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
  right_inv x := by
    show (a * (a⁻¹ * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
  measurable_toFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  measurable_invFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))

theorem rconv_eq_translate {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    (μG : Measure (Mt k r)) (e : Mat k r → ℂ) (W : Mat k r → Wp) (hμ : IsHaarOn (GG k r) μG)
    {y : Mat k r} (hy : y ∈ GG k r) :
    rconv μG e W y = ∫ g, e (y⁻¹ * Matrix.of g) • W (Matrix.of g) ∂μG := by
  have hyu : IsUnit y⁻¹.det := GG_unit (GG_inv hy)
  have hmap : μG.map (lmulM y⁻¹) = μG := hμ.2.2.2 _ (GG_inv hy)
  have hme : MeasurableEmbedding (lmulM (k := k) (r := r) y⁻¹) :=
    (lmulEquiv y⁻¹ hyu).measurableEmbedding
  unfold rconv
  conv_lhs => rw [← hmap]
  rw [hme.integral_map]
  congr 1; funext g
  show e (Matrix.of (lmulM y⁻¹ g)) • W (y * Matrix.of (lmulM y⁻¹ g)) = _
  show e (y⁻¹ * Matrix.of g) • W (y * (y⁻¹ * Matrix.of g)) = _
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GG_unit hy), Matrix.one_mul]

theorem kernel_rconv : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g))) ν ∧ rconv μG (eFun μG σ w) W y = (d : ℂ) • ∫ g, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) ∂ν := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hz, hT, hπ, hμS, _⟩ := hSide
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hun := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hμS
  have hμG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hWeil := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hμG hμS hun hν
  have hFint : Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG :=
    GlobalTheory.T.integrable_besselCoefficient_smul_equivariant k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hI, hEq⟩ := hWeil.2.2.2.1 Wp _ hFint
  have hae : ∀ᵐ x ∂ν, (∫ s, star (coef σ w w (y⁻¹ * Matrix.of (lmulM (Matrix.of s) x))) •
      W (Matrix.of (lmulM (Matrix.of s) x)) ∂μS) =
      be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
    have h0 : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
      rw [ae_iff]; simpa using hWeil.2.1
    filter_upwards [h0] with x hx
    exact GlobalTheory.T.bessel_inner_integral_eq_form k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ W hW y hy x hx
  have hfd : fdegH μG σ w = d :=
    GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality k r σ μG d w hStd.2.2.2.2.2.1 (by
      intro h0; have := hStd.2.2.2.1; rw [h0, norm_zero] at this; exact zero_ne_one this)
  refine ⟨hI.congr hae, ?_⟩
  rw [rconv_eq_translate μG _ W hμG hy]
  have hfun : (fun g : Mt k r => eFun μG σ w (y⁻¹ * Matrix.of g) • W (Matrix.of g)) =
      fun g => (d : ℂ) • (star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) := by
    funext g; simp only [eFun, hfd, coef, smul_smul]
  rw [hfun, integral_smul, hEq, integral_congr_ae hae]

end GlobalTheory.SgInf.KernelRe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSideStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_standard_side : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g))) ν ∧ rconv μG (eFun μG σ w) W y = (d : ℂ) • ∫ g, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) ∂ν := by
  first | exact @GlobalTheory.SgInf.KernelRe.kernel_rconv | exact GlobalTheory.SgInf.KernelRe.kernel_rconv | (intros; apply GlobalTheory.SgInf.KernelRe.kernel_rconv <;> assumption)
end
