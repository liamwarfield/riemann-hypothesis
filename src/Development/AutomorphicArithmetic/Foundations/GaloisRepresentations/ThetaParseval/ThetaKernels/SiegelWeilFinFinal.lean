module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinLt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnfK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PtExK

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AbsConvK
set_option synthInstance.maxHeartbeats 200000

section
set_option linter.style.haveILetI false
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
open ComplexParameterFamilyContinuity
theorem cptDom_k : _root_.PositivityTheory.SiegelWeilFormula.Act.CptDom_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun nb lam 𝓖 h => ?_, fun L uM ν 𝓤 h => ?_⟩
  · have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
    obtain ⟨hlc, hsc, ht2, hbo⟩ := kfour.nA_top hσ d.ok.frame
    obtain ⟨K, hK, hc⟩ := kfour.nF_cocompact hσ d.ok.frame
    obtain ⟨hnb, hlam, hfd, h1⟩ := h
    obtain ⟨𝓖₀, hfd₀, hcpt⟩ := addFD_of_cover' (nF σ d.Y d.b) hK hc lam
    exact ⟨𝓖₀, ⟨hnb, hlam, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
  · obtain ⟨hfr, hν, hfd, h1⟩ := h
    haveI : DiscreteTopology L.ratV := ratVec_discrete (F := F) (E := E) L.n
    haveI : Countable L.ratV := ratVec_countable (F := F) (E := E) L.n
    obtain ⟨K, hK, hc⟩ : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ v, ∃ γ ∈ L.ratV, γ + v ∈ K :=
      ratVec_cocompact (F := F) (E := E) L.n
    obtain ⟨𝓤₀, hfd₀, hcpt⟩ := addFD_of_cover' L.ratV hK hc ν
    exact ⟨𝓤₀, ⟨hfr, hν, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
theorem absConv_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩
  obtain ⟨hTG, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨hnb, hlam, hfd, h1⟩ := h𝓖
  obtain ⟨hfr, hν, hfdU, hU1⟩ := h𝓤
  have cu : Continuous uM := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_uM_k L ⟨hfr, hν, hfdU, hU1⟩
  have cn : Continuous nb := kunf.continuous_nb hnb
  have cφ : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z
  set m : (Fin L.n → AE F E) × nA σ d.Y d.b → d.G := fun p => nb p.2 * (uM p.1 * x) with hm
  have cm : Continuous m := (cn.comp continuous_snd).mul ((cu.comp continuous_fst).mul continuous_const)
  have hKc : IsCompact (closure 𝓤 ×ˢ closure 𝓖) := hc𝓤.prod hc𝓖
  obtain ⟨u, hu, hub⟩ := (hmaj z hz).1 (m '' (closure 𝓤 ×ˢ closure 𝓖)) (hKc.image cm)
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have cψ := kfour.continuous_chr (σ := σ) (Y := d.Y) (b := d.b) hψ.1 T.1.1
  obtain ⟨Mψ, hMψ⟩ := hc𝓖.exists_bound_of_continuousOn cψ.continuousOn
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by rw [hU1]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  have hS : ∀ᵐ p ∂μ, p ∈ closure 𝓤 ×ˢ closure 𝓖 := by
    rw [ae_iff]
    refine measure_mono_null (t := (closure 𝓤)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (closure 𝓖)ᶜ) ?_ ?_
    · intro p hp
      simp only [Set.mem_ofPred_eq, Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
    · have eU : (closure 𝓤)ᶜ ∩ 𝓤 = ∅ := (show Disjoint (closure 𝓤)ᶜ 𝓤 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓤)ᶜ) (h' : y ∈ 𝓤) => hy (subset_closure h')).inter_eq
      have eG : (closure 𝓖)ᶜ ∩ 𝓖 = ∅ := (show Disjoint (closure 𝓖)ᶜ 𝓖 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓖)ᶜ) (h' : y ∈ 𝓖) => hy (subset_closure h')).inter_eq
      refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eU, measure_empty, zero_mul]
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eG, measure_empty, mul_zero]
  have hbd : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, ∀ᵐ p ∂μ, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ≤ |u q| * |Mψ| := by
    intro q
    filter_upwards [hS] with p hp
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, norm_mul]
    refine mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hcq : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) := fun q =>
    (cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)
  have hint : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) μ := fun q =>
    Integrable.of_bound (hcq q).aestronglyMeasurable _ (hbd q)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun p => norm_nonneg _) (fun q => ?_)
    ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))
  calc ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂μ ≤ ∫ _p, |u q| * |Mψ| ∂μ :=
        integral_mono_ae (hint q).norm (integrable_const _) (hbd q)
    _ = |u q| * |Mψ| * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzLeftInvK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem phz_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ rat2 σ d.Y) (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  intro p hp g
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp.1
  obtain ⟨T, hT⟩ := par_rat ht hp.2
  obtain ⟨u, hu⟩ := det_rat hT
  have ha : d.a (p * g) = d.a g := by
    rw [IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]; simp
  have hfp : f (p * g) = f g := Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha, hfp]
theorem eis_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    ∀ γ ∈ rat2 σ d.Y, ∀ g, d.eis f s₁ z (γ * g) = d.eis f s₁ z g :=
  GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z)
theorem fc_dom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 𝓖₀ : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (h₀ : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀)
    (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T g = fc d.B.ψ d.b nb lam 𝓖₀ φ T g := by
  unfold fc
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  refine h.2.2.1.setIntegral_eq h₀.2.2.1 fun β₀ β => ?_
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActTop
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecUnfOfCLawK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CLawExK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FrameDilK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.CL
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rEx_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : ∃ r : ℝ → GroundTheory.Global.IdeleGroup F,
    (∀ τ τ', r (τ + τ') = r τ * r τ') ∧ r 0 = 1 ∧
    (∀ τ, (GroundTheory.Global.IdeleGroup.ideleModule F (r τ) : ℝ) = Real.exp τ) ∧
    (∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ)) ∧
    (∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1) ∧
    (∀ τ, finOne F * (r τ : AF F) = finOne F) := by
  have := d.cm.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let u : ℝ → ℝˣ := fun τ => ⟨Real.exp τ, Real.exp (-τ), by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero],
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]⟩
  let r : ℝ → GroundTheory.Global.IdeleGroup F := fun τ => GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u τ))
  have hu : ∀ τ τ', u (τ + τ') = u τ * u τ' := fun τ τ' => Units.ext (Real.exp_add τ τ')
  have hu0 : u 0 = 1 := Units.ext Real.exp_zero
  have hr1 : ∀ τ, ((r τ : AF F)).1 = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (e.symm (Real.exp τ)) := fun τ => rfl
  have hr2 : ∀ τ, ((r τ : AF F)).2 = 1 := fun τ => rfl
  have hee : ∀ x : ℝ, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm x) = x := fun x => e.apply_symm_apply x
  have hext : ∀ τ, InfinitePlace.Completion.extensionEmbedding w (e.symm (Real.exp τ)) = (Real.exp τ : ℂ) := by
    intro τ
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hee]
  refine ⟨r, fun τ τ' => by simp only [r, hu, map_mul], by simp only [r, hu0, map_one], fun τ => ?_, fun τ => ?_,
    fun τ w' hw' => ?_, fun τ => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding, hw.mult_eq_one, pow_one]
    show ‖e.symm (Real.exp τ)‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), hee,
      Real.norm_of_nonneg (Real.exp_pos τ).le]
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_same]
    exact hext τ
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw', map_one]
  · refine Prod.ext ?_ ?_
    · show (0 : Ainf F) * _ = 0
      rw [zero_mul]
    · show (1 : Af F) * (r τ : AF F).2 = 1
      rw [hr2, mul_one]
theorem frame_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (r : ℝ → GroundTheory.Global.IdeleGroup F)
    (hw : ∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ))
    (ho : ∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1)
    (hf : ∀ τ, finOne F * (r τ : AF F) = finOne F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = dM i₀ ((r τ : AF F) • (1 : AE F E)) ((r (-τ) : AF F) • (1 : AE F E)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hC : Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ)) 0 0
      (Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)) = dM i₀ (Real.exp τ : ℂ) (Real.exp (-τ) : ℂ) := by
    ext u v
    rw [dM_apply]
    rcases u with u | u <;> rcases v with v | v <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.diagonal_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, Matrix.zero_apply] <;>
      by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;> simp_all [Pi.single_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      rw [R.cw_iota_pf w' y, hy, dZ_conj_diag hζ0, hC, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, hw, hw]
    · rw [R.off_w w w' y hw', _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, ho τ w' hw', ho (-τ) w' hw']
      ext u v
      rw [dM_apply, Matrix.one_apply]
      split_ifs <;> rfl
  · rw [R.off_f w y]
    ext u v
    rw [Matrix.smul_apply, Matrix.smul_apply, dM_apply, Matrix.one_apply]
    have e : ∀ t, finOne F • ((r t : AF F) • (1 : AE F E)) = finOne F • (1 : AE F E) := fun t => by
      rw [smul_smul, hf]
    split_ifs <;> simp [e]
theorem par_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    ∃ t, IsPar (R.ι w y) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (2 * τ) ∧
      (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 := by
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ) with hAdef
  set D : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)
  have hy' : mR y = Matrix.fromBlocks A 0 0 D := hy
  obtain ⟨-, hA, -, hoA, hfA, -⟩ := R.frame_diag w y A D hy'
  have h21 : (mR y).toBlocks₂₁ = 0 := by rw [hy', Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar_k d R w y h21
  have hdetA : A.det = (Real.exp τ : ℂ) := by
    rw [hAdef, Matrix.det_diagonal, Finset.prod_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  refine ⟨t, ht, ?_, ?_⟩
  · rw [habs, hy', Matrix.toBlocks_fromBlocks₁₁, hdetA, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos τ).le,
      ← Real.exp_nat_mul]
    norm_num
  · have ht1 := ((kunf.isPar_frame ht0 (R.ι w y) t).1 ht).2
    set P := (inFrame d.b (R.ι w y)).toBlocks₁₁ with hP
    have hcw : ∀ w', d.cw w' t.1 = d.cw w' (incM F t0.1) * d.cw w' P * d.cw w' (incM F (t0⁻¹).1) := by
      intro w'; rw [ht1]; simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul]
    have hI : incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
      rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
    have hT : ∀ w', d.cw w' (incM F t0.1) * d.cw w' (incM F (t0⁻¹).1) = 1 := by
      intro w'; rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, ← Matrix.map_mul, hI, Matrix.map_one _ (map_zero _) (map_one _)]
    have ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1 := fun w' h => by rw [hcw, (hoA w' h).1, Matrix.mul_one, hT]
    have hf : finOne F • t.1 = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
      rw [ht1, ← Matrix.smul_mul, ← Matrix.mul_smul, hfA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hI]
    have hdet : (d.cw w t.1).det = (Real.exp τ : ℂ) := by
      have hXY := congrArg Matrix.det (hT w)
      rw [Matrix.det_mul, Matrix.det_one] at hXY
      rw [hcw, Matrix.det_mul, Matrix.det_mul, hA, hdetA]
      linear_combination ((Real.exp τ : ℝ) : ℂ) * hXY
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (d := d) w t _ rfl ho hf, hdet]
    exact d.chiW_pos w _ (Real.exp_pos τ)
end PositivityTheory.SiegelWeilFormula.Act.CL
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
def CLawEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d),
  ∃ (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G) (κ : Measure ((Fin L.n → AE F E) × AF F)),
    _root_.PositivityTheory.SiegelWeilFormula.Act.CLaw_k R L w₁ cM κ ∧ w₁ ∈ rat2 σ d.Y ∧
    (∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)) ∧
    Continuous cM ∧ κ.IsAddHaarMeasure ∧
    ∃ δ : E, δ ≠ 0 ∧ ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (c.1 j))
      (Matrix.single L.i₀ L.i₀ (c.2 • inclR (F := F) (AF F) δ)) 0 A'
theorem cLawEx_k : _root_.PositivityTheory.SiegelWeilFormula.Act.CLawEx_k := by
  intro F E _ _ _ _ _ σ d R L
  have hε := R.hε
  have hem : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  set e : AE F E := ((R.ε : ℤ) : AE F E) with he_def
  have hee : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨δ, hδ0, hδ⟩ := CL.deltaEx' d.cm R.ε
  obtain ⟨κ, hκ, hsc⟩ := CL.measEx' (F := F) (E := E) L.n d.bs
  let M₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ (1 : E) ((R.ε : ℤ) : E)
  let M₀' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ ((R.ε : ℤ) : E) (1 : E)
  have hW : incM F M₀ = CL.wM L.i₀ (1 : AE F E) e := by
    show M₀.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hW' : incM F M₀' = CL.wM L.i₀ e (1 : AE F E) := by
    show M₀'.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hWW : incM F M₀ * incM F M₀' = 1 := by
    rw [hW, hW']; exact CL.wM_mul L.i₀ _ _ _ _ (one_mul 1) hee
  have hWu : (incM F M₀)ᵀ * kunf.jw d.n e * (incM F M₀).map (cA σ) = kunf.jw d.n e := by
    rw [hW]
    refine CL.wM_unitary L.i₀ (cA σ).toRingHom 1 e e ?_ ?_
    · simp only [AlgHom.toRingHom_eq_coe, map_one, mul_one, hee]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, he_def, map_intCast, one_mul]
  obtain ⟨w₁, hw₁⟩ := kunf.exists_of_frame hε (incM F M₀) (incM F M₀') hWW hWu
  have hw₁' : inFrame d.b w₁ = CL.wM L.i₀ (1 : AE F E) e := hw₁.trans hW
  set δ' : AE F E := inclR (F := F) (AF F) δ with hδ'
  let Mc : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em c.1 (fun j => cA σ (c.1 j)) (c.2 • δ')
  let Mc' : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em (-c.1) (-fun j => cA σ (c.1 j)) (-(c.2 • δ'))
  have hcont : ∀ s : AF F → AF F, Continuous s → ∀ t : (Fin L.n → AE F E) → (Fin L.n → AE F E), Continuous t →
      Continuous fun c : (Fin L.n → AE F E) × AF F =>
        CL.cB L.i₀ L.em (t c.1) (fun j => cA σ (t c.1 j)) (s c.2 • δ') := by
    intro s hs t ht
    refine Continuous.matrix_fromBlocks ?_ ?_ continuous_const ?_
    · exact continuous_const.add (continuous_finsetSum _ fun j _ =>
        cont_single _ _ ((continuous_apply j).comp (ht.comp continuous_fst)))
    · exact cont_single _ _ (Continuous.smul (f := fun c : (Fin L.n → AE F E) × AF F => s c.2) (g := fun _ => δ')
        (hs.comp continuous_snd) continuous_const)
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => cont_single _ _
        ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp (ht.comp continuous_fst))))
  have hMc : Continuous Mc := hcont id continuous_id id continuous_id
  have hMc' : Continuous Mc' := by
    have := hcont (fun a => -a) continuous_neg (fun u => -u) continuous_neg
    convert this using 2 with c
    simp only [Mc', neg_smul, Pi.neg_apply, map_neg]
    rfl
  have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have cA_invol (z : AE F E) : cA σ (cA σ z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
        (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, CL.sigma_sigma_cm d.cm]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcA_z : ∀ a : AF F, cA σ (a • δ') = -(e * (a • δ')) := by
    intro a
    rw [map_smul, hδ', cA_inclR δ, hδ, map_neg, map_mul, map_intCast, smul_neg, mul_smul_comm]
  obtain ⟨cM, hcMc, hcM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.ptEx'_k d hε Mc Mc' hMc hMc'
    (fun c => CL.cB_mul hem c.1 _ _) (fun c => CL.cB_unitary hem (cA σ).toRingHom
      cA_invol e hee c.1 (c.2 • δ') (hcA_z c.2))
  have hfr := fun x y => GlobalTheory.EisBL.DoubledParabolic.inFrame_mul (σ := σ) (Y := d.Y) d.b x y
  refine ⟨w₁, cM, κ, ⟨?_, ?_, ?_⟩, kunf.rat_of_inFrame hw₁, ⟨1, (R.ε : ℤ), one_ne_zero, ?_, ?_⟩, hcMc, hκ,
    ⟨δ, hδ0, fun c => ⟨_, hcM c⟩⟩⟩
  ·
    intro w τ y g hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]
    exact CL.comm_dM L.i₀ _ (L.j_out g) _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    have hy' := CL.isDil_inv hy
    obtain ⟨t, ht, ha, hχ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.par_dil_k d R w L.i₀ hy'
    refine ⟨R.ι w y⁻¹, t, ht, by rw [ha]; ring_nf, hχ, ?_⟩
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, hw₁', _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy', neg_neg]
    exact CL.wM_dM L.i₀ _ _ _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, hrm, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    obtain ⟨sc, hsc1, hsc2⟩ := hsc (r (-τ))
    refine ⟨sc, fun c => ?_, ?_⟩
    · apply kunf.inFrame_injective d.b
      rw [hfr, hfr, hcM, hcM, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]
      have hxy : ((r τ : AF F) • (1 : AE F E)) * ((r (-τ) : AF F) • (1 : AE F E)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, ← Units.val_mul, ← hr0, add_neg_cancel, hr1]; simp
      rw [CL.cB_dM hem _ _ _ _ _ hxy, hsc1]
      congr 1
      simp only [Mc]
      congr 1
      · funext j; exact smul_one_mul _ _
      · funext j; rw [map_smul, smul_one_mul]
      · rw [mul_assoc, smul_one_mul, smul_one_mul, smul_assoc, mul_smul]
    · rw [hsc2, hrm, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, ← _root_.PositivityTheory.SiegelWeilFormula.Atop.LD.n_succ_k L]
      congr 2
      push_cast; ring
  · simp [map_intCast]
  · rw [hw₁']; simp [CL.wM, map_intCast, map_one, he_def]
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
theorem secUnf_of_cLaw_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.CLawEx_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecUnf_k := by
  intro hA hL F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hA F E σ d L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T T' hT nb' lam' 𝓖' hc' hk' => ?_⟩
  obtain ⟨w₁, cM, κ, hlaw, hw, hwf, hcM, hκ, δ, hδ, hcf⟩ := hL F E σ d R L
  have h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ :=
    { nb := hc.1, uM := hU.1, nb' := hc'.1, wr := hw, wf := hwf, cf := hcf, δ0 := hδ }
  obtain ⟨K, hK⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.unf_k R hf z hc hU hT hc' (fun x => ht z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T x) h hcM hκ
  exact ⟨w₁, cM, κ, hlaw, K, fun x => hK x⟩
theorem secUnf_of_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecUnf_k := fun hA => _root_.PositivityTheory.SiegelWeilFormula.Act.secUnf_of_cLaw_k hA _root_.PositivityTheory.SiegelWeilFormula.Act.cLawEx_k
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PsiTContPerK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadZeroMemUnipotent
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def padZeroAlt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0
theorem pad_zero_embedding (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]
theorem pad_zero_outside (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
theorem pad_zero_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact h1 a c
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β i k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0
theorem eps_common_k : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩
theorem pad_zero_mem_unipotent (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this
def padN_k : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_mem_unipotent L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h, add_zero]
theorem prj_padN_k (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding L β.1 a c
theorem continuous_padN_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h]
    exact continuous_const
theorem prj_nF_k {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, hT]
  rfl
theorem padN_nF_k {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]
theorem fiber_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact GlobalTheory.T.haar_measure_split_exact_sequence (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_padN_k L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_nF_k L hγ)
    (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_nF_k L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
instance countableCs_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  infer_instance
theorem cont_E_k {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f)
    (hmaj : ∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
      ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q)
    {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b nb') (x : d.G) :
    Continuous fun β' : nA σ L.Y L.b => ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) := by
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.cos_bij_k L
  have hphz : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_eq_flat_k]
    exact continuous_flat hf.cont (_root_.PositivityTheory.SiegelWeilFormula.kunf.continuous_a_k d) (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z
  have hg : Continuous fun β' : nA σ L.Y L.b => L.j (nb' β') * x :=
    (L.cont.comp (kunf.continuous_nb hnb')).mul continuous_const
  have hterm : ∀ q' β', _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 * (L.j (nb' β') * x)) := by
    intro q' β'
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he q'
    rw [hrep, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z hp₀ hr₀, map_mul, mul_assoc]
  refine continuous_iff_continuousAt.2 fun β₀ => ?_
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (L.j (nb' β₀) * x)
  obtain ⟨u, hu, hbd⟩ := hmaj C hCc
  have hN : (fun β' : nA σ L.Y L.b => L.j (nb' β') * x) ⁻¹' C ∈ 𝓝 β₀ := hg.continuousAt.preimage_mem_nhds hC
  refine (continuousOn_tsum (u := u ∘ Subtype.val ∘ e) (fun q' => ?_) (hu.comp_injective
    (Subtype.val_injective.comp e.injective)) (fun q' β' hβ' => ?_)).continuousAt hN
  · exact (hphz.comp ((L.cont.comp (continuous_const.mul (kunf.continuous_nb hnb'))).mul continuous_const)).continuousOn
  · rw [hterm]
    exact hbd _ hβ' _
theorem per_E_k {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b nb')
    (x : d.G) (β₀ : nA σ L.Y L.b) (h₀ : β₀ ∈ nF σ L.Y L.b) (β' : nA σ L.Y L.b) :
    ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' (β₀ + β')) * x) =
      ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) := by
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y) (fun y : G2 σ L.Y => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j y * x)) := by
    intro γ hγ g
    simp only [map_mul, mul_assoc]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L (Subgroup.mem_inf.1 hγ).1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (Subgroup.mem_inf.1 hγ).2) _
  have h := GlobalTheory.Eis.leftInv_cosetSum hinv (nb' β₀) (kunf.nb_rat hnb' h₀) (nb' β')
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term] at h
  rw [kunf.nb_add hnb']
  exact h
theorem psiT_cont_per_k (T' : nF σ L.Y L.b) :
    Continuous (fun β' : nA σ L.Y L.b => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))) ∧
    ∀ β₀ ∈ nF σ L.Y L.b, ∀ β' : nA σ L.Y L.b,
      d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * (β₀ + β').1)))) =
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1)))) := by
  have hstd := d.ok.good.std
  refine ⟨?_, fun β₀ h₀ β' => ?_⟩
  · have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
    have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
    exact hstd.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  · have h1 := kunf.psi_rat hstd T' ⟨β₀, h₀⟩
    rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, h1, inv_one, one_mul]
theorem firstEq_of_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.FirstEq_k := by
  intro hA F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨t₁, ht₁⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t₂, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨max t₁ t₂, fun z hz nb lam 𝓖 hc hGc nb' lam' 𝓖' hc' hGc' uM ν 𝓤 hU hUc T T' hT x => ?_⟩
  have hz₁ : t₁ < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz₂ : t₂ < z.re := lt_of_le_of_lt (le_max_right _ _) hz
  obtain ⟨hint, hsum⟩ := ht₁ z hz₁ nb lam 𝓖 hc hGc uM ν 𝓤 hU hUc T x
  obtain ⟨e, he'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.cos_bij_k L
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := ⟨by rw [Measure.restrict_apply_univ, hU.2.2.2]; exact ENNReal.one_lt_top⟩
  set ψT : nA σ L.Y L.b → ℂ := fun β' => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))
    with hψT
  set H : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → nA σ L.Y L.b → ℂ := fun q' β' => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) * ψT β' with hH
  have hpt : ∀ q' (pr : (Fin L.n → AE F E) × nA σ d.Y d.b),
      _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x pr = H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L pr.2) := by
    rintro q' ⟨u, β⟩
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he' q'
    obtain ⟨p₁, t, hp₁, hdet, hid⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.key_id_k L hc.1 hc'.1 hU (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') β u x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, hH, hψT]
    rw [hrep, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z hp₀ hr₀, hid, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_par_k hf z hp₁ hdet, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β]
  have hν1 : (ν.restrict 𝓤).real Set.univ = 1 := by
    simp [Measure.real, hU.2.2.2]
  have hkq : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x = fun pr => H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L pr.2) := fun q' => funext (hpt q')
  have htm : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x = ∫ β in 𝓖, H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by
    intro q'
    have h1 : ∀ u, fc d.B.ψ d.b nb lam 𝓖 (fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 * g)) T (uM u * x) =
        ∫ β in 𝓖, H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by
      intro u
      refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
      exact hpt q' (u, β)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.tm_k, h1]
    rw [setIntegral_const]
    simp [Measure.real, hU.2.2.2]
  have hint' : ∀ q', Integrable (fun β => H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) (lam.restrict 𝓖) := by
    intro q'
    have h1 := (hint (e q').1).integral_prod_right
    rw [hkq] at h1
    simpa only [integral_const, hν1, one_smul] using h1
  have hnorm : ∀ q', ∫ pr, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x pr‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      ∫ β in 𝓖, ‖H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)‖ ∂lam := by
    intro q'
    have hI := (hint (e q').1).norm
    rw [integral_prod _ hI]
    simp only [hkq, integral_const, hν1, one_smul]
  have hsum' : Summable fun q' => ∫ β in 𝓖, ‖H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)‖ ∂lam := by
    have h2 := hsum.comp_injective (Subtype.val_injective.comp e.injective)
    exact h2.congr fun q' => hnorm q'
  set G : nA σ L.Y L.b → ℂ := fun β' => (∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x)) * ψT β' with hG
  have hHG : ∀ β', ∑' q', H q' β' = G β' := fun β' => tsum_mul_right
  have hGc : Continuous G := by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.cont_E_k L hf (hmaj z hz₂).1 hc'.1 x).mul (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.psiT_cont_per_k L T').1
  have hGp : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β' := by
    intro β₀ h₀ β'
    simp only [hG, hψT]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.per_E_k L hf hc'.1 x β₀ h₀ β', (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.psiT_cont_per_k L T').2 β₀ h₀ β']
  calc ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
      = ∑' q', _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x :=
        (e.tsum_eq (fun q => _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x)).symm
    _ = ∑' q', ∫ β in 𝓖, H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := tsum_congr htm
    _ = ∫ β in 𝓖, ∑' q', H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by
        haveI : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.countableCs_k L.sd
        exact integral_tsum_of_summable_integral_norm hint' hsum'
    _ = ∫ β in 𝓖, G (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by simp only [hHG]
    _ = ∫ β' in 𝓖', G β' ∂lam' := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.fiber_k L hc hc' G hGc hGp
    _ = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x := by
        simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.first_k, fc, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, mul_one, hG, hψT]
        rfl
end PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act
theorem firstEq_k : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstEq_k := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.firstEq_of_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IndepDomK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocCompactNAK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isClosed_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsClosed (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have e : (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := Set.ext fun β => kunf.mem_nA_iff hε β
  rw [e]
  exact isClosed_eq continuous_id.matrix_transpose (((continuous_id.matrix_map hc).const_smul (((ε : ℤ) : AE F E))).neg)
instance locCompact_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : LocallyCompactSpace (nA σ d.Y d.b) :=
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.isClosed_nA_k d).isClosedEmbedding_subtypeVal.locallyCompactSpace
theorem coef_periodic_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb) (φ : d.G → ℂ)
    (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) (β₀ : nF σ d.Y d.b)
    (β : nA σ d.Y d.b) :
    φ (nb (β₀ +ᵥ β) * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β₀ +ᵥ β).1)))) =
      φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add hN, mul_assoc, hφ _ (kunf.nb_rat hN β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
theorem cj_mp_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    MeasurePreserving (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 v) lam lam := by
  have := h.2.1
  refine ⟨(_root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU h.1 v).measurable, ?_⟩
  have hl := latHaar (nA σ d.Y d.b) lam (nF σ d.Y d.b) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v) (fun x => ⟨fun hx => ?_, fun hx => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hv hx⟩)
    𝓖 h.2.2.1 (by rw [h.2.2.2]; exact one_ne_zero) (by rw [h.2.2.2]; exact ENNReal.one_ne_top)
  · exact hl
  · have := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hv) hx
    rwa [show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v x) = x from _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 v x] at this
theorem fc_conj_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * g) = fc d.B.ψ d.b nb lam 𝓖 φ T g := by
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  let H : nA σ d.Y d.b → ℂ := fun β =>
    φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have e1 : ∀ β, φ (nb β * (uM u * g)) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) := by
    intro β
    have e : nb β * (uM u * g) = uM u * (nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) * g) := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.nb_cj_k hU h.1 u β]; group
    simp only [H]
    rw [e, hφ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_rat_k hU hu), _root_.PositivityTheory.SiegelWeilFormula.Act.C1.trace_cj_k hU h.1 hT]
  have hme : MeasurableEmbedding (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 u).toHomeomorph.measurableEmbedding
  have himg : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) '' 𝓖 = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u x) ∈ 𝓖
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
    · intro hy
      refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y, hy, ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) y
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖) lam := by
    refine h.2.2.1.preimage_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU (neg_mem hu)).quasiMeasurePreserving
      (e := fun γ => ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hu γ.2⟩) ⟨fun γ γ' hγ => ?_, fun γ => ?_⟩ fun γ x => ?_
    · have := congrArg (fun y : nF σ d.Y d.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y.1) hγ
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k] at this
      exact Subtype.ext this
    · refine ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hu) γ.2⟩, Subtype.ext ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) γ.1
    · show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1) + x) = γ.1 + _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) x
      rw [map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
  unfold fc
  simp_rw [e1]
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU hu).setIntegral_image_emb hme H 𝓖, himg,
    hfd.setIntegral_eq h.2.2.1 (fun β₀ β => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.coef_periodic_k d h.1 φ hφ T g β₀ β)]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzJLeftInvK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem range_or_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩
theorem j_par_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp
theorem j_rat_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dite_eq_left hu, dite_eq_left hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dite_eq_left hu, dite_eq_right hv]
      have hv' := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dite_eq_right hu]
    have hu' := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]
theorem phz_j_leftInv_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (p * g) * x) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z (L.j p) ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.j_par_k L hp.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.j_rat_k L hp.2⟩ _
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
theorem indepDom_k : _root_.PositivityTheory.SiegelWeilFormula.Act.IndepDom_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf z
  have hE := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.eis_leftInv_k d hf z
  refine ⟨fun nb lam 𝓖 𝓖₀ h h₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hT x => ?_, fun nb' lam' 𝓖' 𝓖'₀ h' h'₀ T' x => ?_⟩
  · have step1 : ∀ g, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T g = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T g :=
      fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_dom_k d h h₀ _ hE T g
    simp_rw [step1]
    have := hU.2.1
    have : VAddInvariantMeasure L.ratV (Fin L.n → AE F E) ν := ⟨fun c s _ => measure_preimage_add ν c.1 s⟩
    have : Countable L.ratV := by
      have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
      refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
        (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
      obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
      exact ⟨v, Subtype.ext hv.symm⟩
    refine hU.2.2.1.setIntegral_eq hU₀.2.2.1 fun u₀ u => ?_
    show fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM (u₀.1 + u) * x) = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x)
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_conj_k h₀ hU _ hE hT u₀.2]
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_dom_k L.sd h' h'₀ _ (GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_j_leftInv_k L hf z x)) T' 1
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Act
theorem ctSplit_of_k : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k := fun _ _ =>
  _root_.PositivityTheory.SiegelWeilFormula.Act.ctSplit_of_parts_k _root_.PositivityTheory.SiegelWeilFormula.Act.indepDom_k _root_.PositivityTheory.SiegelWeilFormula.Act.cptDom_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k _root_.PositivityTheory.SiegelWeilFormula.Act.firstEq_k (_root_.PositivityTheory.SiegelWeilFormula.Act.secLaw_of_k (_root_.PositivityTheory.SiegelWeilFormula.Act.secUnf_of_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k))
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem siegelWeilStd_k : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_of_ct_k (_root_.PositivityTheory.SiegelWeilFormula.Act.ctSplit_of_k _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k)
end PositivityTheory.SiegelWeilFormula.Fin
end
