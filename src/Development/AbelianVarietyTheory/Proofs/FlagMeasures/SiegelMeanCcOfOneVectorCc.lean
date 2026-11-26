module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquiv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureGaussian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedAdditiveCharacterConductor
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocalDensityValue

def placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Fv F v →+ AF F :=
  (AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom

theorem continuous_placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (placeHom F v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

def localChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (placeHom F v)

theorem isLocalChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) (m : ℤ)
    (hm : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsLocalChar F v (localChar F ψ v) := by
  refine ⟨hψ.1.comp (continuous_placeHom F v), fun t => hψ.2.1 _, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (m + 1))
  have := (hm t).1 fun s _ => h _
  rw [ht, WithZero.exp_le_exp] at this
  omega

end GlobalTheory.LocalDensityValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMeanOfWeilSiegel
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Count GlobalTheory.GaussMean
open Formalism.MainNotions.S (AutInst uMat)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SiegelWeilMean

theorem lintegral_eq_of_meanC {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : μ S < ⊤)
    (G : α → ENNReal) (hG : Measurable G) (hfin : ∫⁻ a in S, G a ∂μ < ⊤) (c : ℝ)
    (h : meanC μ S (fun a => ((G a).toReal : ℂ)) = (c : ℂ)) :
    ∫⁻ a in S, G a ∂μ = μ S * ENNReal.ofReal c := by
  by_cases h0 : μ S = 0
  · rw [h0, zero_mul, setLIntegral_measure_zero _ _ h0]
  have h1 : (μ S).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, hS.ne⟩
  unfold meanC at h
  beta_reduce at h
  rw [integral_complex_ofReal, integral_toReal hG.aemeasurable (ae_lt_top hG hfin.ne), Complex.real_smul] at h
  have h2 : (μ S).toReal⁻¹ * (∫⁻ a in S, G a ∂μ).toReal = c := by exact_mod_cast h
  rw [← h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin.ne, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_toReal hS.ne, ENNReal.mul_inv_cancel h0 hS.ne, one_mul]

theorem exists_transport (I : AutInst) (T : HA (AF I.F) I.cm.sig I.J ≃ₜ* I.GA)
    (hT : ∀ h, (show HR (AF I.F) I.cm.sig I.J from h) ∈ HFinIn (AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset)
    (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ Measurable T ∧ μ S = I.muA μf fund ∧
      ∀ f : I.GA → ENNReal, ∫⁻ h in S, f (T h) ∂μ = ∫⁻ x in fund, f x ∂(I.muA μf) := by
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by unfold Formalism.REAL.muG; infer_instance
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  haveI : (I.muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  haveI : BorelSpace I.GA := inferInstance
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := inferInstance
  obtain ⟨Γ, hΓ, -, -, hF⟩ := GlobalTheory.RatDiscrete.rational_points I
  let e : HA (AF I.F) I.cm.sig I.J ≃ᵐ I.GA := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e ((I.muA μf).map e.symm) (I.muA μf) :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hmem : ∀ g : Γ, (show HR (AF I.F) I.cm.sig I.J from T.symm g) ∈ HFinIn (AF I.F) I.cm.sig I.J := fun g => by
    refine (hT (T.symm g)).2 ?_
    have : T (T.symm g) = g := T.apply_symm_apply _
    exact this.symm ▸ (hΓ ▸ g.2 : g.1 ∈ I.GFset)
  refine ⟨(I.muA μf).map e.symm, e ⁻¹' fund, T.symm.isHaarMeasure_map _, ?_, e.measurable,
    hp.measure_preimage_equiv _, fun f => hp.setLIntegral_comp_preimage_emb e.measurableEmbedding f _⟩
  refine (hF μf fund hfund).preimage_of_equiv hp.quasiMeasurePreserving
    (e := fun g => ⟨T.symm g, hmem g⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun g x => ?_
  · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
  · exact ⟨⟨T b.1, by rw [← SetLike.mem_coe, hΓ]; exact (hT _).1 b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
  · change T (T.symm g * x) = g * T x
    rw [map_mul, T.apply_symm_apply]

theorem const_eq {ι κ : Type} [Fintype κ] (q : ι → ℝ) (hq : ∀ u, 0 < q u) (m : ι → ℤ)
    (hm : (Function.support m).Finite) (a : ι → ℝ) (Lv : ℝ) (ha : HasProd a Lv⁻¹) (lam g : κ → ℝ)
    (hlam : ∀ v, lam v ≠ 0) (w : ℝ) (hw : 0 < w) (n f : ℕ) (hf : Fintype.card κ = f)
    (hp : ∏ᶠ u, q u ^ m u = (2 * w) ^ f * ∏ v, |lam v|) :
    ((∏ v, 2 ^ n * |lam v| ^ ((n : ℝ) - 1 / 2) * g v : ℝ) : ℂ) *
      ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) =
      (((2 * w) ^ ((f : ℝ) / 2) * (w ^ (n * f))⁻¹ / Lv * ∏ v, g v : ℝ) : ℂ) := by
  have hout : ∀ u ∉ hm.toFinset, m u = 0 := fun u hu => by simpa using hu
  have h1 : HasProd (fun u => (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)))
      (∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ))) :=
    hasProd_prod_of_ne_finset_one fun u hu => by simp [hout u hu]
  have h2 : ∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) =
      ((2 * w) ^ f * ∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) := by
    rw [Real.finsetProd_rpow _ _ (fun u _ => (zpow_pos (hq u) _).le) _, ← hp,
      finprod_eq_prod_of_mulSupport_subset _ (s := hm.toFinset)]
    intro u hu
    by_contra h
    exact hu (by simp [hout u h])
  have h3 := (h1.mul ha).map Complex.ofRealHom Complex.continuous_ofReal
  have h4 : ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) = _ := h3.tprod_eq
  rw [h4, h2, Complex.ofRealHom_eq_coe, ← Complex.ofReal_mul]
  congr 1
  have hl : 0 < ∏ v, |lam v| := Finset.prod_pos fun v _ => abs_pos.2 (hlam v)
  have h5 : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) * (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = 1 := by
    rw [← Real.rpow_add hl]; simp
  have h6 : ((2 * w) ^ f) ^ ((1 / 2 : ℝ) - (n : ℝ)) = (2 * w) ^ ((f : ℝ) / 2) * ((2 * w) ^ (n * f))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (2 * w) (n * f),
      ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
    congr 1; push_cast; ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf,
    Real.finsetProd_rpow _ _ (fun v _ => abs_nonneg _) _, Real.mul_rpow (by positivity) hl.le, h6, mul_pow, pow_mul 2]
  have : (2 ^ n : ℝ) ^ f ≠ 0 := by positivity
  have h7 : (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = ((∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2))⁻¹ :=
    eq_inv_of_mul_eq_one_right h5
  have : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) ≠ 0 := by positivity
  rw [h7]
  field_simp


end GlobalTheory.SiegelWeilMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ArchimedeanDensityProductTestFunctionAtSign
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ArchimedeanDensityProductTestFunctionAtSign
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.RealDensityCc

open GlobalTheory.GaussMean.RealDensity GlobalTheory.GaussMean.Density Filter Topology

theorem selfDual_complex_eq {ι : Type} [Fintype ι] {n : ℕ} (d : ι → Fin n → ℝ) (hd : ∀ v i, d v i ≠ 0)
    (μ : Measure (ι → Fin n → ℂ))
    (h : SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ v, ∑ i, d v i * ((x v i).re * (y v i).re + (x v i).im * (y v i).im) : ℝ) : ℂ)))) :
    μ = ENNReal.ofReal (∏ v, ∏ i, |d v i|) • (volume : Measure (ι → Fin n → ℂ)) := by
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.ReImVolume.exists_reIm_measurePreserving ι n
  have h1 := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag (ι × Fin n × Bool) (fun k => d k.1 k.2.1) (fun k => hd _ _) _
    (selfDual_map T h fun x y => by
      congr 3
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, (hT' _ _ _).1, (hT' _ _ _).2, mul_add])
  have he : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  refine he.map_injective ?_
  rw [h1, Measure.map_smul, hT.map_eq]
  congr 2
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, Real.mul_self_sqrt (abs_nonneg _)]
  exact hT.measurable.aemeasurable

theorem eq_zero_of_cubes {ι : Type} [Fintype ι] {K : (ι → ℝ) → ℂ} {U : Set (ι → ℝ)} (hK : ContinuousOn K U)
    {b : ι → ℝ} (hU : U ∈ 𝓝 b)
    (h : ∀ r : ℝ, 0 < r → Set.Icc b (fun v => b v + r) ⊆ U → ∫ x in Set.Icc b (fun v => b v + r), K x = 0) :
    K b = 0 := by
  by_contra hne
  have he : 0 < ‖K b‖ := norm_pos_iff.2 hne
  have h0 : ∀ᶠ x in 𝓝 b, x ∈ U ∧ dist (K x) (K b) < ‖K b‖ / 2 :=
    (show ∀ᶠ x in 𝓝 b, x ∈ U from hU).and
      (Metric.tendsto_nhds.1 (hK.continuousAt hU) _ (half_pos he))
  obtain ⟨d, hd, hδ⟩ := Metric.eventually_nhds_iff.1 h0
  set r := d / 2 with hr
  have hr0 : 0 < r := half_pos hd
  have hin : ∀ x ∈ Set.Icc b (fun v => b v + r), dist x b < d := fun x hx => by
    refine lt_of_le_of_lt (b := r) ?_ (half_lt_self hd)
    rw [dist_pi_le_iff hr0.le]
    intro v
    have h3 := hx.1 v
    have h4 := hx.2 v
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hsub : Set.Icc b (fun v => b v + r) ⊆ U := fun x hx => (hδ (hin x hx)).1
  have hk : 0 < r ^ Fintype.card ι := pow_pos hr0 _
  have hvol : volume.real (Set.Icc b (fun v => b v + r)) = r ^ Fintype.card ι := by
    rw [Measure.real, Real.volume_Icc_pi_toReal (fun v => by simp [hr0.le])]
    simp
  have hfin : volume (Set.Icc b (fun v => b v + r)) < ⊤ := isCompact_Icc.measure_lt_top
  have h1 : ∫ x in Set.Icc b (fun v => b v + r), (K x - K b) = - ((r ^ Fintype.card ι) • K b) := by
    rw [integral_sub (hK.mono hsub).integrableOn_Icc continuousOn_const.integrableOn_Icc,
      setIntegral_const, hvol, h r hr0 hsub, zero_sub]
  have h2 : ‖∫ x in Set.Icc b (fun v => b v + r), (K x - K b)‖ ≤ ‖K b‖ / 2 * r ^ Fintype.card ι := by
    rw [← hvol]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    rw [← dist_eq_norm]
    exact (hδ (hin x hx)).2.le
  rw [h1, norm_neg, norm_smul, Real.norm_of_nonneg hk.le] at h2
  nlinarith

theorem setIntegral_box {ι : Type} [Fintype ι] {X : Type} [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (q : ι → X → ℝ) (hq : ∀ v, Measurable (q v)) (φ : ι → X → ℝ) (a c : ι → ℝ) :
    ∫ y in (fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c, ∏ v, φ v (y v) =
      ∏ v, ∫ y in q v ⁻¹' Set.Icc (a v) (c v), φ v y := by
  have hm : MeasurableSet ((fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c) :=
    measurableSet_Icc.preimage
      (Measurable.of_eval fun v => (hq v).comp (measurable_pi_apply v))
  rw [← integral_indicator hm,
    ← Finset.prod_congr rfl fun v _ => integral_indicator (measurableSet_Icc.preimage (hq v)),
    ← integral_fintype_prod_volume_eq_prod]
  congr 1
  funext y
  by_cases hy : y ∈ (fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c
  · rw [Set.indicator_of_mem hy]
    exact Finset.prod_congr rfl fun v _ => (Set.indicator_of_mem (s := q v ⁻¹' Set.Icc (a v) (c v))
      ⟨hy.1 v, hy.2 v⟩ _).symm
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨v, hv⟩ : ∃ v, y v ∉ q v ⁻¹' Set.Icc (a v) (c v) := by
      by_contra! h
      exact hy ⟨fun v => (h v).1, fun v => (h v).2⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)).symm

theorem density_eq_prod_of_isDens (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool)
    (φ : ι → (Fin n → ℂ) → ℝ) (D : ι → ℝ → ℝ) (hD : ∀ v, IsDens (ε v) (φ v) (D v)) (G : (ι → ℝ) → ℂ)
    (hG : ContinuousOn G {b | ∀ v, b v ≠ 0})
    (h : ∀ S : Set (ι → ℝ), IsCompact S → S ⊆ {b | ∀ v, b v ≠ 0} →
      ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, φ v (y v) : ℝ) : ℂ) =
        ∫ b in S, G b)
    (b : ι → ℝ) (hb : ∀ v, b v ≠ 0) : G b = ((∏ v, D v (b v) : ℝ) : ℂ) := by
  have hH : ContinuousOn (fun x : ι → ℝ => ((∏ v, D v (x v) : ℝ) : ℂ)) {b | ∀ v, b v ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_finsetProd _ fun v _ =>
      (hD v).1.comp (continuous_apply v).continuousOn fun x hx => hx v)
  have hU : {b : ι → ℝ | ∀ v, b v ≠ 0} ∈ 𝓝 b :=
    Filter.eventually_all.2 fun v => (continuous_apply v).continuousAt.eventually_ne (hb v)
  refine sub_eq_zero.1 (eq_zero_of_cubes (hG.sub hH) hU fun r hr hsub => ?_)
  simp only [Pi.sub_apply]
  rw [integral_sub (hG.mono hsub).integrableOn_Icc (hH.mono hsub).integrableOn_Icc, ← h _ isCompact_Icc hsub,
    integral_complex_ofReal, integral_complex_ofReal, sub_eq_zero,
    setIntegral_box (fun v => qEps (ε v)) (fun v => (continuous_qEps (ε v)).measurable)]
  congr 1
  refine Eq.trans ?_ (setIntegral_box (fun _ => id) (fun _ => measurable_id) D b fun v => b v + r).symm
  refine Finset.prod_congr rfl fun v _ => (hD v).2 _ isCompact_Icc fun t ht => ?_
  classical
  have := hsub (a := Function.update b v t) ⟨fun w => ?_, fun w => ?_⟩ v
  · simpa using this
  · by_cases hw : w = v
    · subst hw; simpa using ht.1
    · simp [hw]
  · by_cases hw : w = v
    · subst hw; simpa using ht.2
    · simp [hw, hr.le]

theorem density_at_sign : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ (lamv : InfinitePlace I.F → ℝ) (χ : Ainf I.F → ℂ), (∀ v, lamv v ≠ 0) → (∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) → ∀ (μi : Measure (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E)) (νi : Measure (Ainf I.F)), SelfDual μi (fun X Y => χ (BR (Ainf I.F) I.cm.sig I.J X Y)) → SelfDual νi (fun s t => χ (s * t)) → ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ), (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v) ∧ IsDens (I.ε v) (φ v) (D v)) → ∀ Fi : Ainf I.F → ℂ, IsContDensityOn μi (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) id νi {c | IsUnit c} (fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) Fi → ∀ s : Bool, Fi (sgn (Ainf I.F) s) = ((∏ v, 2 ^ I.n * |lamv v| ^ ((I.n : ℝ) - 1 / 2) * D v (sgn ℝ s) : ℝ) : ℂ) := by
  intro I θ hθ lam χ hlam hχ μ ν hμ hν φ D hφ Fi hF s
  obtain ⟨a, ha⟩ := exists_coord_base I θ hθ
  obtain ⟨T, hT⟩ := exists_coord_space I θ hθ
  have hform := fun v => trace_form I v (θ v) (hθ v)
  have h2 : Module.finrank I.F I.E = 2 := I.cm.deg2
  have : FiniteDimensional I.F I.E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  have : IsModuleTopology (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf I.F ⊗[I.F] I.E) := IsModuleTopology.isTopologicalRing (Ainf I.F) _
  have : SecondCountableTopology (Ainf I.F) := a.toHomeomorph.secondCountableTopology
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := I.F) (E := I.E) (Ainf I.F)
  have : SecondCountableTopology (Ainf I.F ⊗[I.F] I.E) := e0.secondCountableTopology
  have : BorelSpace (Ainf I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have : BorelSpace (Ainf I.F) := ⟨rfl⟩
  have hmul : ∀ x y v, a (x * y) v = a x v * a y v := fun x y v => by
    have : ((a (x * y) v : ℝ) : ℂ) = (a x v : ℝ) * (a y v : ℝ) := by
      rw [← ha, ← ha, ← ha, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact_mod_cast this
  have hone : ∀ v, a 1 v = 1 := fun v => by
    have : ((a 1 v : ℝ) : ℂ) = 1 := by
      rw [← ha]; exact map_one (θ v)
    exact_mod_cast this
  have hsgn : a (sgn (Ainf I.F) s) = fun _ => sgn ℝ s := by
    funext v
    cases s <;> simp [sgn, hone]
  have hhalf : ∀ v, a (algebraMap I.F (Ainf I.F) (1 / 2)) v = 1 / 2 := fun v => by
    have h1 : algebraMap I.F (Ainf I.F) (1 / 2) + algebraMap I.F (Ainf I.F) (1 / 2) = 1 := by
      rw [← map_add (f := _), add_halves, map_one]
    have := hone v
    rw [← h1, map_add (f := _), Pi.add_apply] at this
    linarith
  have htr : ∀ (X Y : Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) v,
      a (Algebra.trace (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) (hR (Ainf I.F) I.cm.sig I.J (X 0) (Y 0))) v =
        ∑ i, (if I.ε v i then 2 else -2) * ((T X v i).re * (T Y v i).re + (T X v i).im * (T Y v i).im) :=
    fun X Y v => by
      have := hform v (X 0) (Y 0)
      rw [ha] at this
      rw [hT, hT]
      exact_mod_cast this
  have hq : ∀ X, a (qR (Ainf I.F) I.cm.sig I.J (X 0)) = fun v => qEps (I.ε v) (T X v) := fun X => by
    funext v
    rw [qR, hmul, hhalf, htr, qEps, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    split_ifs <;> ring
  have hν' := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag _ lam hlam _ (selfDual_map a hν fun x y => by
    rw [hχ]; simp only [ha, Complex.ofReal_re, hmul])
  have hμ' := selfDual_complex_eq (fun v i => lam v * (if I.ε v i then 2 else -2))
    (fun v i => mul_ne_zero (hlam v) (by split_ifs <;> norm_num)) _ (selfDual_map T hμ fun x y => by
      rw [hχ]; simp only [ha, Complex.ofReal_re, BR, Fin.sum_univ_one, htr, Finset.mul_sum, mul_assoc])
  have hc : (∏ v, ∏ i, |lam v * (if I.ε v i then 2 else -2)|) = ∏ v, (2 * |lam v|) ^ I.n := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => 2 * |lam v|) fun i _ => by
      rw [abs_mul]; split_ifs <;> simp [mul_comm]]
    simp
  rw [hc] at hμ'
  set c : ℝ := ∏ v, (2 * |lam v|) ^ I.n with hcdef
  set c' : ℝ := ∏ v, √|lam v| with hc'def
  have hc0 : 0 < c := Finset.prod_pos fun v _ => pow_pos (mul_pos two_pos (abs_pos.2 (hlam v))) _
  have hc'0 : 0 < c' := Finset.prod_pos fun v _ => Real.sqrt_pos.2 (abs_pos.2 (hlam v))
  have heT : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hea : MeasurableEmbedding a := a.toHomeomorph.measurableEmbedding
  have hunit : ∀ x : Ainf I.F, (∀ v, a x v ≠ 0) → IsUnit x := fun x hx => by
    refine IsUnit.of_mul_eq_one (a.symm fun v => (a x v)⁻¹) (a.injective ?_)
    funext v
    rw [hmul, ContinuousAddEquiv.apply_symm_apply, hone, mul_inv_cancel₀ (hx v)]
  have key := density_eq_prod_of_isDens _ I.n I.ε φ D (fun v => (hφ v).2.2)
    (fun b => ((c' / c : ℝ) : ℂ) * Fi (a.symm b))
    (continuousOn_const.mul (hF.1.comp a.symm.continuous.continuousOn fun b hb =>
      hunit _ (by simpa using hb))) (fun S hS hSU => by
      have h1 := hF.2 (a ⁻¹' S) (a.toHomeomorph.isCompact_preimage.2 hS) fun x hx => hunit x (hSU hx)
      have h3 := hea.setIntegral_map (μ := ν) (fun b => Fi (a.symm b)) S
      have h4 := heT.setIntegral_map (μ := μ) (fun y => ((∏ v, φ v (y v) : ℝ) : ℂ))
        ((fun y v => qEps (I.ε v) (y v)) ⁻¹' S)
      simp only [ContinuousAddEquiv.symm_apply_apply] at h3
      have h5 : (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) ⁻¹' (id '' (a ⁻¹' S)) =
          T ⁻¹' ((fun y v => qEps (I.ε v) (y v)) ⁻¹' S) := by
        ext X
        simp only [Set.image_id, Set.mem_preimage, hq]
      rw [h5, ← h3] at h1
      simp only [← hT] at h1
      rw [← h4, hμ', hν', Measure.restrict_smul, Measure.restrict_smul, integral_smul_measure,
        integral_smul_measure, ENNReal.toReal_ofReal hc0.le, ENNReal.toReal_ofReal hc'0.le,
        Complex.real_smul, Complex.real_smul] at h1
      have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
      rw [integral_const_mul, Complex.ofReal_div, div_mul_eq_mul_div, ← h1, mul_div_cancel_left₀ _ hcc])
    (fun _ => sgn ℝ s) (fun _ => by cases s <;> simp [sgn])
  rw [← hsgn, ContinuousAddEquiv.symm_apply_apply] at key
  have hcc : ((c' / c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hc'0 hc0).ne'
  refine mul_left_cancel₀ hcc ?_
  rw [key, ← Complex.ofReal_mul, hcdef, hc'def, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  have hl : 0 < |lam v| := abs_pos.2 (hlam v)
  rw [Real.rpow_sub hl, Real.rpow_natCast, Real.sqrt_eq_rpow, mul_pow]
  have : 0 < |lam v| ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hl _
  field_simp

end GlobalTheory.GaussMean.RealDensityCc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ArchimedeanDensityProductTestFunctionAtSignStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_density_product_testFunction_at_sign : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ (lamv : InfinitePlace I.F → ℝ) (χ : Ainf I.F → ℂ), (∀ v, lamv v ≠ 0) → (∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) → ∀ (μi : Measure (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E)) (νi : Measure (Ainf I.F)), SelfDual μi (fun X Y => χ (BR (Ainf I.F) I.cm.sig I.J X Y)) → SelfDual νi (fun s t => χ (s * t)) → ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ), (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v) ∧ IsDens (I.ε v) (φ v) (D v)) → ∀ Fi : Ainf I.F → ℂ, IsContDensityOn μi (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) id νi {c | IsUnit c} (fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) Fi → ∀ s : Bool, Fi (sgn (Ainf I.F) s) = ((∏ v, 2 ^ I.n * |lamv v| ^ ((I.n : ℝ) - 1 / 2) * D v (sgn ℝ s) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.GaussMean.RealDensityCc.density_at_sign | exact GlobalTheory.GaussMean.RealDensityCc.density_at_sign | (intros; apply GlobalTheory.GaussMean.RealDensityCc.density_at_sign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousDensitySelfDualLatticeIndicatorAtUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousDensitySelfDualLatticeIndicatorAtUnit
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeContDensity

theorem contDensity_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v → ∀ ψ : AddChar (Fv F v) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsLocalChar v ψ → ∀ n : ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.DualExponent v ψ n → ∀ L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L → ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), SdW F E σ M J (Fv F v) ψ 1 μ → SdR (Fv F v) ψ ν → ∀ g : Fv F v → ℂ, IsContDensityOn μ (fun X => qR (Fv F v) σ J (X 0)) id ν {c | c ≠ 0} ({X | X 0 ∈ L}.indicator 1) g → ∀ β : Fv F v, Valued.v β = 1 → g β = (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ v hv ψ hψ n hn L hL μ ν hμ hν g hg β hβ

  have H : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.SelfDualLatticeDensity :=
    GlobalTheory.LocalDensityCompare.localDensity_iff.1
      (GlobalTheory.LatticeDensity.localDensity_of_selfDualLatticeLemmas
        GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas)
  obtain ⟨η, hη⟩ := GlobalTheory.LocalDensityCompare.exists_eta F E v
  have hEta : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsEtaAt F E v η :=
    (GlobalTheory.LocalDensityCompare.isEtaAt_iff F E v hσ.2.2.1 η).2 ⟨hv, hη⟩
  have key := (H F E σ hσ M J hM hJ v η hEta ψ hψ).2 n hn L
    ((GlobalTheory.LocalDensityCompare.isSelfDualLattice_iff v σ J L).1 hL) μ hμ ν hν

  have hβ' : Valued.v (β - β) < 1 := by simp
  have hgβ := (key.2.2 β hβ).2 g hg β hβ'
  rw [hgβ, ← GlobalTheory.LocalDensityCompare.dens_eq v n M η hη]

end GlobalTheory.LatticeContDensity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousDensitySelfDualLatticeIndicatorAtUnitStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousDensity_selfDualLatticeIndicator_at_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v → ∀ ψ : AddChar (Fv F v) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsLocalChar v ψ → ∀ n : ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.DualExponent v ψ n → ∀ L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L → ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), SdW F E σ M J (Fv F v) ψ 1 μ → SdR (Fv F v) ψ ν → ∀ g : Fv F v → ℂ, IsContDensityOn μ (fun X => qR (Fv F v) σ J (X 0)) id ν {c | c ≠ 0} ({X | X 0 ∈ L}.indicator 1) g → ∀ β : Fv F v, Valued.v β = 1 → g β = (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LatticeContDensity.contDensity_unit | exact GlobalTheory.LatticeContDensity.contDensity_unit | (intros; apply GlobalTheory.LatticeContDensity.contDensity_unit <;> assumption)
end
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Count GlobalTheory.GaussMean
open Formalism.MainNotions.S (AutInst uMat)
open scoped TensorProduct Pointwise Topology

noncomputable section

namespace GlobalTheory.OneVectorMean

theorem continuous_qEps {n : ℕ} (ε : Fin n → Bool) : Continuous (qEps ε) := by
  unfold qEps
  fun_prop

theorem qEps_smul {n : ℕ} (ε : Fin n → Bool) (r : ℝ) (y : Fin n → ℂ) : qEps ε (r • y) = r ^ 2 * qEps ε y := by
  simp only [qEps, Finset.mul_sum, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_isDens {n : ℕ} {ε : Fin n → Bool} {φ : (Fin n → ℂ) → ℝ} {D : ℝ → ℝ} (hc : Continuous φ)
    (hK : HasCompactSupport φ) (h0 : ∀ y, 0 ≤ φ y) (hD : IsDens ε φ D) {β : ℝ} (hβ : β ≠ 0) (hz : D β = 0)
    {y₀ : Fin n → ℂ} (hy : qEps ε y₀ = β) : φ y₀ = 0 := by
  by_contra hne
  have hpos : 0 < φ y₀ := lt_of_le_of_ne (h0 _) (Ne.symm hne)
  set a := φ y₀ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hq := continuous_qEps ε
  have hnb : {p : ℝ × (Fin n → ℂ) | a < φ (p.1 • p.2)} ∈ 𝓝 ((1 : ℝ), y₀) :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp only [Set.mem_setOf_eq, one_smul]; linarith)
  obtain ⟨V, hV, U', hU', hVU⟩ := mem_nhds_prod_iff.1 hnb
  obtain ⟨ρ, hρ, hU⟩ := Metric.mem_nhds_iff.1 hU'
  set U := Metric.ball y₀ ρ
  haveI : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using measure_ball_lt_top⟩
  let m : Measure ℝ := (volume.restrict U).map (qEps ε)
  let J : Set ℝ := (fun t => √(β / t)) ⁻¹' (V ∩ Set.Icc (1 / 2) 2) ∩ Metric.ball β 1
  have hJ : J ∈ 𝓝 β := by
    have : ContinuousAt (fun t => √(β / t)) β := by fun_prop (disch := exact hβ)
    refine Filter.inter_mem (this.preimage_mem_nhds ?_) (Metric.ball_mem_nhds _ one_pos)
    rw [div_self hβ, Real.sqrt_one]
    exact Filter.inter_mem hV (Icc_mem_nhds (by norm_num) (by norm_num))
  set d := Module.finrank ℝ (Fin n → ℂ)
  have hint : Integrable φ := hc.integrable_of_hasCompactSupport hK
  have hDc : ContinuousAt D β := hD.1.continuousAt (isOpen_ne.mem_nhds hβ)
  have key : ∀ c : NNReal, 0 < c → m J ≤ (c • volume : Measure ℝ) J := fun c hc0 => by
    refine (Besicovitch.vitaliFamily m).measure_le_of_frequently_le _ Measure.AbsolutelyContinuous.rfl J
      fun t ht => (Besicovitch.tendsto_filterAt m t).frequently (Filter.Eventually.frequently ?_)
    set e : ℝ := a * (1 / 2) ^ d * c / 4 with he
    have he0 : 0 < e := by positivity
    have h1 : {s | s ≠ 0 ∧ ‖D s‖ ≤ e} ∈ 𝓝 β :=
      Filter.inter_mem (isOpen_ne.mem_nhds hβ) (hDc.norm.eventually (eventually_le_nhds (by simpa [hz] using he0)))
    obtain ⟨δ₀, hδ₀, h2⟩ := Metric.nhds_basis_closedBall.mem_iff.1 h1
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ₀ / 4 by positivity)] with δ hδ
    obtain ⟨⟨hrV, hr1, hr2⟩, -⟩ := ht
    set r := √(β / t) with hr
    have hbt : 0 < β / t := Real.sqrt_pos.1 (by linarith)
    have ht0 : t ≠ 0 := by rintro rfl; simp at hbt
    have hrr : r ^ 2 * t = β := by rw [hr, Real.sq_sqrt hbt.le]; field_simp
    have hsub : Metric.closedBall β (4 * δ) ⊆ {s | s ≠ 0 ∧ ‖D s‖ ≤ e} :=
      (Metric.closedBall_subset_closedBall (by linarith [hδ.2])).trans h2
    have h3 := hD.2 _ (isCompact_closedBall β (4 * δ)) fun s hs => (hsub hs).1
    have h4 : ∫ s in Metric.closedBall β (4 * δ), D s ≤ e * (2 * (4 * δ)) := by
      refine (Real.le_norm_self _).trans ((norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top
        fun s hs => (hsub hs).2).trans_eq ?_)
      rw [Real.volume_real_closedBall (by linarith [hδ.1])]
    set A := qEps ε ⁻¹' Metric.closedBall t δ ∩ U
    set B := {y | qEps ε y ∈ Metric.closedBall β (4 * δ)}
    have h5 : r • A ⊆ {y | ENNReal.ofReal a ≤ ENNReal.ofReal (φ y)} ∩ B := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨ENNReal.ofReal_le_ofReal (hVU (Set.mk_mem_prod hrV (hU hy2))).le, ?_⟩
      change qEps ε (r • y) ∈ Metric.closedBall β (4 * δ)
      rw [qEps_smul, Metric.mem_closedBall, Real.dist_eq, ← hrr, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul (by change r ≤ 2 at hr2; change 1 / 2 ≤ r at hr1; nlinarith) hy1 (abs_nonneg _) (by norm_num)
    have h6 : ENNReal.ofReal (a * (1 / 2) ^ d) * volume A ≤
        ENNReal.ofReal (a * (1 / 2) ^ d) * (c * ENNReal.ofReal (2 * δ)) := by
      calc ENNReal.ofReal (a * (1 / 2) ^ d) * volume A ≤ ENNReal.ofReal a * volume (r • A) := by
            rw [Measure.addHaar_smul, ENNReal.ofReal_mul ha0.le, mul_assoc]
            gcongr
            exact (pow_le_pow_left₀ (by norm_num) hr1 _).trans (le_abs_self _)
        _ ≤ ENNReal.ofReal a * volume.restrict B {y | ENNReal.ofReal a ≤ ENNReal.ofReal (φ y)} := by
            exact mul_le_mul_right ((measure_mono h5).trans (Measure.le_restrict_apply _ _)) _
        _ ≤ ∫⁻ y in B, ENNReal.ofReal (φ y) := mul_meas_ge_le_lintegral hc.measurable.ennreal_ofReal _
        _ = ENNReal.ofReal (∫ y in B, φ y) :=
            (ofReal_integral_eq_lintegral_ofReal hint.integrableOn (Filter.Eventually.of_forall h0)).symm
        _ ≤ ENNReal.ofReal (e * (2 * (4 * δ))) := ENNReal.ofReal_le_ofReal (h3 ▸ h4)
        _ = _ := by
            rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg, ← ENNReal.ofReal_mul (by positivity), he]
            congr 1
            ring
    have h7 : m (Metric.closedBall t δ) = volume A := by
      rw [Measure.map_apply hq.measurable measurableSet_closedBall,
        Measure.restrict_apply (hq.measurable measurableSet_closedBall)]
    change m (Metric.closedBall t δ) ≤ c * volume (Metric.closedBall t δ)
    rw [h7, Real.volume_closedBall]
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top).1 h6
  have hfin : volume J ≠ ⊤ := ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hlim : Filter.Tendsto (fun c : NNReal => (c : ENNReal) * volume J) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ENNReal.Tendsto.mul_const (ENNReal.continuous_coe.tendsto (0 : NNReal)) (Or.inr hfin)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hm0 : m J ≤ 0 := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
  have hp : 0 < volume (qEps ε ⁻¹' J ∩ U) := Measure.measure_pos_of_mem_nhds _
    (Filter.inter_mem (hq.continuousAt.preimage_mem_nhds (hy ▸ hJ)) (Metric.ball_mem_nhds _ hρ))
  exact absurd ((Measure.le_restrict_apply _ _).trans ((Measure.le_map_apply hq.aemeasurable J).trans hm0)) hp.not_ge

theorem lintegral_lt_top_of_meanC {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (G : α → ENNReal)
    (hG : Measurable G) (hfin : ∀ a, G a ≠ ⊤) (h : meanC μ S (fun a => ((G a).toReal : ℂ)) ≠ 0) :
    ∫⁻ a in S, G a ∂μ < ⊤ := by
  have h1 : Integrable (fun a => ((G a).toReal : ℂ)) (μ.restrict S) := by
    by_contra h1
    exact h (by unfold meanC; rw [integral_undef h1, smul_zero])
  exact ((integrable_toReal_iff hG.aemeasurable (Filter.Eventually.of_forall hfin)).1 (by simpa using h1.re)).lt_top

variable (I : AutInst) (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ)


open Classical in
def term (x : I.GA) (y : Fin I.n → I.E) : ℝ :=
  if y ∈ lamX I x then ∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)) else 0

theorem term_nonneg (h0 : ∀ v y, 0 ≤ φ v y) (x : I.GA) (y : Fin I.n → I.E) : 0 ≤ term I φ x y := by
  unfold term
  split_ifs
  · exact Finset.prod_nonneg fun v _ => h0 _ _
  · exact le_rfl

theorem measurable_term (hc : ∀ v, Continuous (φ v)) (y : Fin I.n → I.E) :
    Measurable fun x : I.GA => ENNReal.ofReal (term I φ x y) := by
  classical
  obtain ⟨h1, -⟩ := GlobalTheory.StabUnfold.gaussAt_meas_inv I y
  have h2 : ∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) =>
      φ v (((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)) := fun v => by
    have hc' : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
      simp only [GlobalTheory.StabUnfold.uMat_inv_eq]
      exact Units.continuous_coe_inv.comp continuous_subtype_val
    exact ((hc v).comp ((hc'.matrix_mul continuous_const).matrix_mulVec continuous_const)).measurable
  unfold term
  exact (Measurable.ite (measurable_snd h1.measurableSet)
    (Finset.measurable_prod _ fun v _ => (h2 v).comp ((measurable_pi_apply v).comp measurable_fst))
    measurable_const).ennreal_ofReal

theorem finite_term (hK : ∀ v, HasCompactSupport (φ v)) (x : I.GA) : {y | term I φ x y ≠ 0}.Finite := by
  have hb : ∀ v, ∃ C : ℝ, ∀ z ∈ tsupport (φ v), ‖(I.P v * uMat (x.1 v)) *ᵥ z‖ ≤ C := fun v =>
    (hK v).isCompact.exists_bound_of_continuousOn (continuous_const.matrix_mulVec continuous_id).continuousOn
  choose C hC using hb
  obtain ⟨B, hB⟩ := (Set.finite_range C).bddAbove
  refine (GlobalTheory.RatDiscrete.finite_bounded (lamX I x)
    (Module.Finite.iff_fg.2 (GlobalTheory.PointLattice.lamX_selfDual I x).2.1) B).subset fun y hy => ?_
  have hy : term I φ x y ≠ 0 := hy
  unfold term at hy
  have hx : y ∈ lamX I x := by
    by_contra hx
    exact hy (if_neg hx)
  rw [if_pos hx] at hy
  refine ⟨hx, fun τ i => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.RatDiscrete.exists_place I τ
  have h1 := hC v _ (subset_tsupport _ (Finset.prod_ne_zero_iff.1 hy v (Finset.mem_univ v)))
  have h2 : IsUnit (I.P v * uMat (x.1 v)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((I.P_unit v).mul (Units.isUnit _))
  rw [← Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h2, Matrix.one_mulVec] at h1
  rw [hv]
  exact (norm_le_pi_norm (fun i => I.φ v (y i)) i).trans (h1.trans (hB ⟨v, rfl⟩))

theorem qEps_frame (s : Bool) (y : Fin I.n → I.E) (hy : star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s) (v : InfinitePlace I.F)
    (g : Formalism.REAL.UJ (I.ε v)) : qEps (I.ε v) (((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)) = sgn ℝ s := by
  have hφ : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  have hs : star (fun i => I.φ v (y i)) = fun i => I.φ v (star y i) := by
    funext i; simp [hφ]
  have hg : (uMat g⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * uMat g⁻¹ = Formalism.REAL.Jm (I.ε v) := g⁻¹.2
  have hF : ((uMat g)⁻¹ * (I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * ((uMat g)⁻¹ * (I.P v)⁻¹) = I.J.map (I.φ v) := by
    rw [← GlobalTheory.StabUnfold.frame_inv_form I v, GlobalTheory.StabUnfold.uMat_inv_eq, Matrix.conjTranspose_mul]
    conv_rhs => rw [← hg]
    simp only [Matrix.mul_assoc]
  apply Complex.ofReal_injective
  rw [GlobalTheory.StabUnfold.ofReal_qEps_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hF, hs]
  have e : ((sgn ℝ s : ℝ) : ℂ) = I.φ v (sgn I.E s) := by
    unfold sgn; split_ifs <;> simp
  rw [e, ← hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, mulVec, map_sum]

theorem hE_eq (y : Fin I.n → I.E) : hE I.cm.sig I.J y y = star y ⬝ᵥ (I.J *ᵥ y) := by
  simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem sum_eq (β : I.E) (x : I.GA) :
    (∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β},
      ENNReal.ofReal (∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))) =
      ∑' X : {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = β}, ENNReal.ofReal (term I φ x (X.1 0)) := by
  rw [tsum_subtype {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = β}
    fun X => ENNReal.ofReal (term I φ x (X 0)), ← (Equiv.funUnique (Fin 1) (Fin I.n → I.E)).symm.tsum_eq]
  refine (tsum_subtype {y : Fin I.n → I.E | y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β} fun y =>
    ENNReal.ofReal (∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)))).trans
    (tsum_congr fun y => ?_)
  by_cases h : star y ⬝ᵥ (I.J *ᵥ y) = β
  · rw [Set.indicator_of_mem (a := (Equiv.funUnique (Fin 1) (Fin I.n → I.E)).symm y)
      (by exact (hE_eq I y).trans h)]
    change _ = ENNReal.ofReal (term I φ x y)
    unfold term
    by_cases hy : y ∈ lamX I x
    · rw [Set.indicator_of_mem (by exact ⟨hy, h⟩), if_pos hy]
    · rw [Set.indicator_of_notMem (by exact fun h' => hy h'.1), if_neg hy, ENNReal.ofReal_zero]
  · have h1 : (Equiv.funUnique (Fin 1) (Fin I.n → I.E)).symm y ∉
        {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = β} := fun h' => by
      have h'' : hE I.cm.sig I.J y y = β := h'
      exact h ((hE_eq I y).symm.trans h'')
    rw [Set.indicator_of_notMem (by exact fun h' => h h'.2), Set.indicator_of_notMem h1]

theorem sum_ne_top (hK : ∀ v, HasCompactSupport (φ v)) (A : Set (Fin 1 → Fin I.n → I.E)) (x : I.GA) :
    ∑' X : A, ENNReal.ofReal (term I φ x (X.1 0)) ≠ ⊤ := by
  have h := (finite_term I φ hK x).preimage (f := fun X : A => X.1 0)
    fun X _ Y _ hXY => Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact hXY)
  rw [tsum_eq_sum (s := h.toFinset) fun X hX => by
    have : term I φ x (X.1 0) = 0 := by simpa using hX
    rw [this, ENNReal.ofReal_zero]]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top

theorem test_eq_term (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ))
    (hθ : ∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) (T : HA (AF I.F) I.cm.sig I.J ≃ₜ* I.GA)
    (hf : ∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _))
    (hi : ∀ v h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J (θ v) h * I.P v)
    (h : HA (AF I.F) I.cm.sig I.J) (X : Fin 1 → Fin I.n → I.E) :
    ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (projInf (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 i)) : ℝ) : ℂ) *
      {Y : Fin 1 → Fin I.n → Af I.F ⊗[I.F] I.E | Y 0 ∈ Formalism.MainNotions.StandardLattice.latHat I.F I.E (I.L : Set (Fin I.n → I.E))}.indicator
        (1 : (Fin 1 → Fin I.n → Af I.F ⊗[I.F] I.E) → ℂ) (projFin (h⁻¹ • ratTup (F := I.F) (AF I.F) X)) =
      (term I φ (T h) (X 0) : ℂ) := by
  have e0 : ∀ i, (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 i =
      ∑ j, (HA.mat (AF I.F) I.cm.sig I.J h⁻¹).1 i j * ((1 : AF I.F) ⊗ₜ[I.F] X 0 j) := fun i => rfl
  have e1 : projFin (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 ∈ Formalism.MainNotions.StandardLattice.latHat I.F I.E (I.L : Set (Fin I.n → I.E)) ↔
      X 0 ∈ lamX I (T h) := by
    rw [GlobalTheory.T.mem_adelicLatticeClosure_iff_swap_mem_span, (GlobalTheory.PointLattice.lamX_selfDual I (T h)).1, show (T h).2⁻¹ = (T h⁻¹).2 by rw [map_inv]; rfl, hf]
    refine iff_of_eq (congrArg (· ∈ I.Lf) (funext fun i => ?_))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [projFin, e0, map_sum, map_mul, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have e2 : ∀ v, ((I.P v)⁻¹ *ᵥ fun i => θ v (projInf (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 i)) =
      ((uMat ((T h).1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (X 0 i) := fun v => by
    rw [GlobalTheory.StabUnfold.uMat_inv_eq, show ((T h).1 v)⁻¹ = (T h⁻¹).1 v by rw [map_inv]; rfl, hi,
      Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)),
      ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    let p : AF I.F ⊗[I.F] I.E →+* Ainf I.F ⊗[I.F] I.E :=
      (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)).toRingHom
    have e := RingHom.map_mulVec ((θ v).comp p) (HA.mat (AF I.F) I.cm.sig I.J h⁻¹).1
      (ratTup (F := I.F) (AF I.F) X 0) i
    refine e.trans ?_
    have e2 : ((θ v).comp p) ∘ ratTup (F := I.F) (AF I.F) X 0 = fun i => I.φ v (X 0 i) := by
      funext j
      rw [← (hθ v).1]
      show θ v (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) (1 ⊗ₜ X 0 j)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e2]
    rfl
  unfold term
  by_cases hx : X 0 ∈ lamX I (T h)
  · rw [if_pos hx, Set.indicator_of_mem (by exact e1.2 hx), Pi.one_apply, mul_one]
    simp only [e2]
  · rw [if_neg hx, Set.indicator_of_notMem (by exact fun h' => hx (e1.1 h')), mul_zero, Complex.ofReal_zero]

theorem test_smooth (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ))
    (hθ : ∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v))
    (hs : ∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ v)) (hK : ∀ v, HasCompactSupport (φ v))
    (Φ : (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) → ℂ)
    (hΦ : Φ = fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) :
    Continuous Φ ∧ HasCompactSupport Φ ∧
      ∀ (N : ℕ) (e : (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ ∘ e.symm) := by
  obtain ⟨T, hT⟩ := GlobalTheory.GaussMean.RealDensity.exists_coord_space I θ hθ
  let Ψ : (InfinitePlace I.F → Fin I.n → ℂ) → ℂ := fun z => ((∏ v, φ v (z v) : ℝ) : ℂ)
  have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ :=
    Complex.ofRealCLM.contDiff.comp (contDiff_prod fun v _ => (hs v).comp (contDiff_apply ℝ _ v))
  have hΨK : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun v => (hK v).isCompact) fun z hz => ?_
    obtain ⟨v, hv⟩ : ∃ v, z v ∉ tsupport (φ v) := by simpa using hz
    simp only [Ψ]
    rw [Finset.prod_eq_zero (f := fun v => φ v (z v)) (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport (f := φ v) hv),
      Complex.ofReal_zero]
  have e0 : Φ = Ψ ∘ T := by
    funext X
    simp only [hΦ, Ψ, Function.comp_apply, hT]
  rw [e0]
  refine ⟨hΨ.continuous.comp T.continuous, hΨK.comp_homeomorph T.toHomeomorph, fun N e _ he => ?_⟩
  exact hΨ.comp ((e.symm.trans T.toAddEquiv).toAddMonoidHom.toRealLinearMap (T.continuous.comp he)).contDiff

theorem siegelMeanCc_of_oneVectorCc : OneVectorCc → SiegelMeanCc := by
  intro hW I hn s μf _ _ fund hfund
  obtain ⟨hCM, hJ, T, hT1, hT2, hT3⟩ := GlobalTheory.T.exists_adelic_unitaryGroup_models_equiv I
  obtain ⟨a1, b1⟩ := hW I.F I.E I.cm.sig hCM I.n I.J hJ
  choose θ hθ using fun v => (GlobalTheory.Mem.VolEmb.existsUnique_infEmb _ _ _ hCM (I.φ v)).exists
  obtain ⟨μ, S, hμ, hS, hTm, hvol, hint⟩ := GlobalTheory.SiegelWeilMean.exists_transport I T hT1 μf fund hfund
  have hfin : μ S < ⊤ := (a1.2 μ hμ).2 S hS
  refine ⟨hvol ▸ hfin, fun φ D hφ => ?_⟩
  have hc : ∀ v, Continuous (φ v) := fun v => (hφ v).1.continuous
  have hK : ∀ v, HasCompactSupport (φ v) := fun v => (hφ v).2.1
  have h0 : ∀ v y, 0 ≤ φ v y := fun v => (hφ v).2.2.1
  have hs1 : ∀ (R : Type) [Ring R] [Nontrivial R], sgn R s ≠ 0 := fun R _ _ => by cases s <;> simp [sgn]
  by_cases hD : ∏ v, D v (sgn ℝ s) = 0
  · obtain ⟨v, -, hv⟩ := Finset.prod_eq_zero_iff.1 hD
    rw [hD, mul_zero, ENNReal.ofReal_zero, mul_zero]
    refine (lintegral_congr fun x => ENNReal.tsum_eq_zero.2 fun y => ?_).trans lintegral_zero
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (eq_zero_of_isDens (hc v) (hK v) (h0 v) (hφ v).2.2.2 (hs1 ℝ) hv
      (qEps_frame I s y.1 y.2.2 v _)), ENNReal.ofReal_zero]
  have hL : Submodule.IsLattice I.E I.L := Submodule.IsLattice.of_fg I.E I.L_fg
  have hLfull : Submodule.IsFullLattice I.E I.L :=
    { toIsLattice := hL, span_eq_top := I.L_span }
  haveI : FiniteDimensional I.F I.E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  let b := Module.finBasis I.F I.E
  obtain ⟨g1, g2, g3⟩ := test_smooth I φ θ hθ (fun v => (hφ v).1) hK _ rfl
  have hΦ := test_eq_term I φ θ hθ T hT2 fun v => hT3 v (θ v) (hθ v)
  have hsg : ∀ (R : Type) [CommRing R] [Algebra I.F R], algebraMap I.F R (sgn I.F s) = sgn R s := fun R _ _ => by
    cases s <;> simp [sgn]
  obtain ⟨⟨ψ, hψ⟩, hB⟩ := b1 hn (sgn I.F s) (hs1 _) _ b _ _ _ _ g1 g2 g3
    ⟨GlobalTheory.T.isSchwartzBruhat_indicator_localLatticeCompletion I.F I.E I.n I.L hLfull, (GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice I.F I.E I.n _ b I.L hLfull).mono fun v hv => by rw [hv],
      GlobalTheory.T.indicator_completedLattice_eq_finprod_local I.F I.E I.n I.L hLfull⟩ fun _ => rfl
  obtain ⟨⟨μi, hμi⟩, ⟨νi, hνi⟩, ⟨μv, hμv⟩, ⟨νv, hνv⟩, hQ⟩ := ((hB ψ hψ).2 μ hμ).2 S hS
  obtain ⟨Fi, Fl, hFi, hFl, -, hmean⟩ := hQ μi νi μv νv hμi hνi hμv hνv
  obtain ⟨lam, m, hlam, hψi, hm, hdual, hprod⟩ := GlobalTheory.T.adelic_character_frequencies_and_conductor_product I θ hθ ψ hψ
  obtain ⟨hE1, hE2, hE3⟩ := GlobalTheory.T.cm_euler_product_discr_unramified I I.n (by omega)
  obtain ⟨n1, n2, n3, -, n5, -⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hreal := GlobalTheory.T.archimedean_density_product_testFunction_at_sign I θ hθ lam _ hlam hψi μi νi hμi hνi φ D (fun v => ⟨hc v, hK v, (hφ v).2.2.2⟩) Fi hFi s
  have hloc : ∀ u, Fl u (algebraMap I.F (Fv I.F u) (sgn I.F s)) =
      (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ m u) ^ ((1 / 2 : ℝ) - (I.n : ℝ)) *
        (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta I.F I.E u ^ I.n * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ I.n)⁻¹) : ℝ) : ℂ) := fun u => by
    obtain ⟨Lv, h1, h2⟩ := GlobalTheory.T.exists_selfDualLattice_completion_maxOrder I.F I.E I.cm.sig I.n I.J I.L hJ hL I.L_dual u
    refine GlobalTheory.T.continuousDensity_selfDualLatticeIndicator_at_unit I.F I.E I.cm.sig hCM I.n (by omega) I.J hJ u (hE3 u) (GlobalTheory.LocalDensityValue.localChar I.F ψ u)
      (GlobalTheory.LocalDensityValue.isLocalChar I.F ψ hψ u (m u) (hdual u)) (m u) (hdual u) Lv h1
      _ _ (hμv u) (hνv u) _ (by simpa only [h2] using hFl u) _ ?_
    rw [hsg]
    cases s <;> simp [sgn]
  have hw : 0 < Formalism.HermitianLatticesTheory.vInv I.E := by linarith
  rw [hsg I.E, hsg (Ainf I.F), hreal, tprod_congr hloc, GlobalTheory.SiegelWeilMean.const_eq _
    (fun u => zero_lt_one.trans (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard I.F u))
    m hm _ _ hE1 lam _ hlam (Formalism.HermitianLatticesTheory.vInv I.E) hw I.n I.f n5 (by rw [← hE2]; exact hprod)] at hmean
  rw [← hint, ← hvol]
  haveI : Countable I.E := (Module.finBasis ℚ I.E).equivFun.toEquiv.countable_iff.2 inferInstance
  simp only [sum_eq I φ]
  have hG : Measurable fun h : HA (AF I.F) I.cm.sig I.J =>
      ∑' X : {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = sgn I.E s},
        ENNReal.ofReal (term I φ (T h) (X.1 0)) :=
    Measurable.tsum fun X => (measurable_term I φ hc _).comp hTm
  have hM : meanC μ S (fun h => ((∑' X : {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = sgn I.E s},
      ENNReal.ofReal (term I φ (T h) (X.1 0))).toReal : ℂ)) =
      ((meanConst I.E I.n * ∏ v, D v (sgn ℝ s) : ℝ) : ℂ) := by
    unfold meanConst
    rw [n1, ← hmean]
    congr 1
    funext h
    rw [ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top, Complex.ofReal_tsum]
    exact tsum_congr fun X => by rw [ENNReal.toReal_ofReal (term_nonneg _ _ h0 _ _), ← hΦ]
  have hL0 := (GlobalTheory.DensityEuler.hasProd_eulerFac I.cm.cmUnram I.n (by omega)).2
  have hc0 : 0 < meanConst I.E I.n := by unfold meanConst; positivity
  exact GlobalTheory.SiegelWeilMean.lintegral_eq_of_meanC μ S hfin _ hG
    (lintegral_lt_top_of_meanC μ S _ hG (fun h => sum_ne_top I φ hK _ _)
      (hM ▸ Complex.ofReal_ne_zero.2 (mul_ne_zero hc0.ne' hD))) _ hM

end GlobalTheory.OneVectorMean
