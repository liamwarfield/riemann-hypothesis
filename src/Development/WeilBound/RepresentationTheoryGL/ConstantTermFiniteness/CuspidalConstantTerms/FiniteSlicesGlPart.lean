module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutOfMemAutForms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaxCompactRealPointsOfOrthonormalFrames
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsBlockPoint
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryAdelicUnipotentLift
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerEndMemLeftInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
open Matrix GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UAut

theorem isRealLine_oneP (D : D7) (θ : InfF D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) :
    GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  obtain ⟨-, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hZ : Xᴴ * V.gram.map (embOverOf D τ).1 + V.gram.map (embOverOf D τ).1 * X = 0 := hX
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SiegelSet.exists_isRealLine (isCMExt_host D) (h2 V) (embOverOf D τ) hZ
  refine ⟨placeOf D τ, embOverOf D τ, X, hZ, fun t => ⟨_, ?_, hγ t⟩⟩
  rw [oneP, ← hγ t, GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), atTau_archEquiv hθ V _ rfl]

end GlobalTheory.UAut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_one_parameter_isRealOneParamSubgroupAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  first | exact @GlobalTheory.UAut.isRealLine_oneP | exact GlobalTheory.UAut.isRealLine_oneP | (intros; apply GlobalTheory.UAut.isRealLine_oneP <;> assumption)
end
end

section -- merged from Development.WeilBound.HeckeVectors.SmoothVectors.ContinuousUnits.LocInCompT
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open GlobalTheory.CuspRep

namespace CompanionTheory.D.gk.Br.LIC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem continuous_infGL [_root_.NumberField.IsTotallyComplex E] : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem continuous_finGL : Continuous (finGL E a) := by
  have hs : Continuous (sFin E) := (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sFin E))) (continuous_const.add (continuous_id.matrix_map hs))


omit [NumberField E] in
theorem continuous_toUnits_Kinf : Continuous fun k : Kinf E a => (Unitary.toUnits k : GL (Fin a) (Cinf E)) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩

theorem continuous_infGL_toUnits [_root_.NumberField.IsTotallyComplex E] :
    Continuous fun k : Kinf E a => infGL E a (Unitary.toUnits k) :=
  continuous_infGL.comp continuous_toUnits_Kinf

end CompanionTheory.D.gk.Br.LIC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.IsCuspidalCompBlockEmb
section -- merged from Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.IntegralSectionEqConstTermOn
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Cusp.Shear.Rg

theorem exists_measurable_addSection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N : Subgroup G) [DiscreteTopology Γ]
    (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) (s : V → G) (π : N → V), Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) →
    (∀ (a : N) (v : V), (a : G) = s v → π a = v) → (∀ v ∈ Λ, s v ∈ Γ) →
    ∃ B : Set V, MeasurableSet B ∧ ∀ v : V, ∃! w : Λ, (w : V) + v ∈ B := _root_.GlobalTheory.Cusp.Shear.exists_measurable_addSection

theorem integral_section_eq_constTermOn : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ]
    [LocallyCompactSpace N] [LocallyCompactSpace N'], N' ≤ N → (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [MeasurableSpace V] [BorelSpace V] (Λ : AddSubgroup V) (s : V → G) (π : N → V),
      Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) → Continuous π →
      (∀ a b : N, π (a * b) = π a + π b) → (∀ (a : N) (v : V), (a : G) = s v → π a = v) →
      (∀ a : N, π a = 0 ↔ (a : G) ∈ N') → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ φ : G → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ φ → Continuous φ → (∀ m ∈ N', ∀ g, φ (m * g) = φ g) →
      ∀ (μ : MeasureTheory.Measure V) (𝓕 : Set V), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Λ 𝓕 μ →
        ∀ x : G, ∫ v in 𝓕, φ (s v * x) ∂μ = μ.real 𝓕 • GlobalTheory.Cusp.constTermOn Γ N φ x := by
  intro G _ _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ Λ s π hsc hmul hs hπc hπmul hπs hker hsΓ hπΓ
    φ hφ hφc hN' μ 𝓕 hμ h𝓕 x

  let s' : V → N := fun v => ⟨s v, hs v⟩
  have hs'c : Continuous s' := hsc.subtype_mk _
  have hleft : Function.LeftInverse π s' := fun v => hπs _ v rfl
  have hemb : Topology.IsEmbedding s' := hleft.isEmbedding hπc hs'c
  haveI : SecondCountableTopology V := hemb.secondCountableTopology
  haveI : T2Space V := hemb.t2Space
  haveI : Countable Λ := Function.Injective.countable (f := fun w : Λ => (⟨s w, hsΓ _ w.2⟩ : Γ)) fun a b h =>
    Subtype.ext (hleft.injective (Subtype.ext (congrArg Subtype.val h : s a = s b)))
  let e := prodHomeo hle hs hsc hπc hπmul hπs hker
  let ν : Measure N := ((Measure.haar : Measure N').prod μ).map e
  haveI : ν.IsHaarMeasure := isHaarMeasure_map_prodHomeo G Γ N N' hle hn hc hc' V s π hs hsc hπc hπmul hπs hker hmul μ hμ
  obtain ⟨B, hBm, hB⟩ := exists_measurable_addSection G Γ N V Λ s π hsc hmul hs hπs hsΓ
  let A := stdDom (Γ.subgroupOf N')
  have hAm : MeasurableSet A := measurableSet_stdDom _
  have hD : IsFundamentalDomain (Γ.subgroupOf N) (e '' (A ×ˢ B)) ν :=
    isFundamentalDomain_image_prod G Γ N N' hle hn V Λ s π hs hsc hπc hπmul hπs hker hmul hsΓ hπΓ A B hAm hBm
      (existsUnique_stdDom _) hB ν
  have hep : MeasurePreserving e ((Measure.haar : Measure N').prod μ) ν := ⟨e.continuous.measurable, rfl⟩
  have hemb' : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding

  have hI : ∫ n in e '' (A ×ˢ B), φ (n * x) ∂ν =
      (Measure.haar : Measure N').real A • ∫ v in B, φ (s v * x) ∂μ := by
    rw [hep.setIntegral_image_emb hemb', ← Measure.prod_restrict]
    have h1 : ∀ z : N' × V, φ ((e z : G) * x) = φ (s z.2 * x) := fun z => by
      rw [prodHomeo_apply, mul_assoc]; exact hN' _ z.1.2 _
    simp only [h1]
    rw [integral_fun_snd (fun v => φ (s v * x)), measureReal_restrict_apply_univ]
  have hM : ν (e '' (A ×ˢ B)) = Measure.haar A * μ B := by
    change ((Measure.haar : Measure N').prod μ).map e _ = _
    rw [hemb'.map_apply, e.preimage_image, Measure.prod_prod]
  have hA0 : (Measure.haar : Measure N') A ≠ 0 := (isFundamentalDomain_stdDom _ _).measure_ne_zero (NeZero.ne _)
  have hAt : (Measure.haar : Measure N') A ≠ ⊤ := hc'.measure_ne_top (isFundamentalDomain_stdDom _ _)
  have hDt := hc.measure_ne_top hD
  have hD0 := hD.measure_ne_zero (NeZero.ne ν)
  rw [hM] at hDt hD0
  have hBt : μ B ≠ ⊤ := fun h => hDt (by rw [h, ENNReal.mul_top hA0])
  have hB0 : μ B ≠ 0 := fun h => hD0 (by rw [h, mul_zero])

  have hBF : IsAddFundamentalDomain Λ B μ := .mk' hBm.nullMeasurableSet fun v => by
    simpa [AddSubgroup.vadd_def, vadd_eq_add] using hB v
  have hf : ∀ (w : Λ) (v : V), φ (s ((w : V) + v) * x) = φ (s v * x) := fun w v => by
    rw [hmul, mul_assoc]; exact hφ _ (hsΓ _ w.2) _
  rw [h𝓕.setIntegral_eq hBF (fun w v => hf w v), measureReal_def, h𝓕.measure_eq hBF, constTermOn_eq hD hφ x, hI,
    measureReal_def, hM, measureReal_def, ENNReal.toReal_mul, smul_smul, smul_smul]
  have ha : ((Measure.haar : Measure N') A).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hA0, hAt⟩
  have hb : (μ B).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hB0, hBt⟩
  rw [show (μ B).toReal * (((Measure.haar : Measure N') A).toReal * (μ B).toReal)⁻¹ *
      ((Measure.haar : Measure N') A).toReal = 1 by field_simp, one_smul]

end GlobalTheory.Cusp.Shear.Rg

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory

namespace GlobalTheory.BlockForms.CuspConst.Rg

theorem continuous_unip (E : Type) [Field E] [NumberField E] (d r' : ℕ) :
    Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => GlobalTheory.CuspRep.unip x := by
  have hn : Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => (GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [GlobalTheory.CuspRep.nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn


open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary in
theorem isCuspidal_comp_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        GlobalTheory.CuspRep.IsCuspidal (fun x => ψ (ι x * g₀)) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW K _ S l d h ι hι _ hS hk hl ψ hψ g₀ _
  intro r' hr0 hr1 _ _ μ 𝓕 hμ h𝓕 g
  let k : Fin r := ⟨l + r' - 1, by omega⟩
  have hkv : k.val + 1 = l + r' := by simp only [k]; omega
  have hkS : k ∉ S := hS k (by simp only [k]; omega) (by simp only [k]; omega)
  have hSS : S ⊂ insert k S := Finset.ssubset_insert hkS
  set U := GlobalTheory.StdPar.unip σ J X (insert k S) with hU
  set U₀ := GlobalTheory.StdPar.unip σ J X S with hU₀
  have hle : U₀ ≤ U := GlobalTheory.T.standardParabolicUnipotent_mono F E σ hσ n J hJ r X Y hW _ S (Finset.subset_insert _ _)
  haveI : LocallyCompactSpace U₀ := (GlobalTheory.StdPar.isClosed_unip S hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace U := (GlobalTheory.StdPar.isClosed_unip _ hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have cS := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW S
  have cS' := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW (insert k S)
  have esub : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → (ratPts σ J ⊓ U).subgroupOf N = (ratPts σ J).subgroupOf N := by
    intro N hN
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hN x.2⟩⟩
  have cinf : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → Cocompact (ratPts σ J) N → Cocompact (ratPts σ J ⊓ U) N := by
    intro N hN hc
    unfold Cocompact
    rw [esub hN]
    exact hc
  have hfΓ : LeftInv (ratPts σ J ⊓ U) ψ := fun γ hγ g => by
    obtain ⟨m, hm, hmL, ν, hν, e⟩ := GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hσ n J hJ r X Y hW S (insert k S) (Finset.subset_insert _ _) γ hγ.1 hγ.2
    rw [e, mul_assoc, hψ.1.leftM m hm hmL, hψ.1.leftN ν hν]
  have hnorm : ∀ p ∈ U, ∀ u ∈ U₀, p * u * p⁻¹ ∈ U₀ := by
    intro p hp u hu
    by_cases hS0 : S = ∅
    · subst hS0
      rw [hU₀, GlobalTheory.StdPar.unip_empty, Subgroup.mem_bot] at hu ⊢
      simp [hu]
    obtain ⟨mS, hmS, hmS'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
      S.max'_mem _, fun k hk => S.le_max' k hk⟩
    have hσσ := sigma_sigma hσ
    have eS := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ hσ n J hJ r X Y hW S mS hmS hmS'
    have hCS : IsIsoCols σ J (GlobalTheory.StdPar.initCols X mS) := isIsoCols_of_isWittFrame hW hσσ hJ mS.2
    rw [hU₀, eS] at hu ⊢
    exact conj_mem_unipFlag hJ hσσ hCS _ (GlobalTheory.ConstTrans.unip_le_parFlag F E σ hσ n J hJ r X Y hW (insert k S) S mS
      (Finset.subset_insert _ _) hmS hmS' hp) hu
  obtain ⟨π, hπc, hπm, hπs, hπk, hπr⟩ := GlobalTheory.T.exists_blockProjection_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv
  have hrat := GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints F E σ hσ n J hJ r X Y hW l d h ι hι
  have hιc := GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries F E σ hσ n J hJ r X Y hW l d h ι hι
  have hsN := GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv

  have h0 : constTermOn (ratPts σ J ⊓ U) U ψ (ι g * g₀) = 0 := by
    obtain ⟨μN, 𝓕N, h1, h2, h3⟩ := exists_mass_one cS'
    rw [constTermOn_eq_of_measure_eq_one ((esub le_rfl).symm ▸ h2) h3 hfΓ]
    exact (hψ.2 _ hSS μN 𝓕N h1 h2 h3 (ι g * g₀)).symm
  have key := GlobalTheory.Cusp.Shear.Rg.integral_section_eq_constTermOn (GAd σ J) (ratPts σ J ⊓ U) U U₀ hle hnorm (cinf le_rfl cS') (cinf hle cS)
    (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) (GlobalTheory.CuspRep.ratN E d r') (fun x => ι (GlobalTheory.CuspRep.unip x)) π
    (hιc.comp (continuous_unip E d r')) (fun v w => by rw [GlobalTheory.CuspRep.unip_add, map_mul]) hsN hπc hπm hπs hπk
    (fun v hv => by
      obtain ⟨x, rfl⟩ := hv
      refine ⟨?_, hsN _⟩
      have := GlobalTheory.CuspRep.unip_algebraMap (a := d) (r := r') x
      exact this ▸ hrat _)
    (fun a ha => hπr a ha.1) ψ hfΓ hψ.1.cont (fun m hm g => hψ.1.leftN m hm g) μ 𝓕 hμ h𝓕 (ι g * g₀)
  rw [h0, smul_zero] at key
  simpa only [map_mul, mul_assoc] using key

end GlobalTheory.BlockForms.CuspConst.Rg

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.EnvRepAllInjective
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps.Rg

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem polyFun_mem (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (P : PolyE V) : polyFun θ V P ∈ SmF θ V := GlobalTheory.CentralOps.polyFun_mem_smF D θ V R P

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction D θ V R τ X P


open Classical in
theorem aeval_matDer_single {T : Type} {n : ℕ} (τ τ' : T) (a b c d : Fin n) :
    MvPolynomial.aeval (fun p : T × Fin n × Fin n => if p.2.1 = p.2.2 then (1 : ℂ) else 0)
      (matDer τ (Matrix.single a b (1 : ℂ)) (MvPolynomial.X (τ', c, d) -
        MvPolynomial.C (if c = d then (1 : ℂ) else 0))) = if (τ, a, b) = (τ', c, d) then 1 else 0 := by
  rw [map_sub, MvPolynomial.derivation_C, sub_zero, matDer_X]
  by_cases h : τ' = τ
  · subst h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [if_true, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.single_apply,
      Algebra.algebraMap_self, RingHom.id_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Prod.mk.injEq, true_and]
  · simp only [h, if_false, map_zero]
    rw [if_neg]; intro h'; exact h (congrArg Prod.fst h').symm

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem polyFun_add (P Q : PolyE V) : polyFun θ V (P + Q) = polyFun θ V P + polyFun θ V Q := by
  funext g; simp [polyFun]

theorem polyFun_smul (c : ℂ) (P : PolyE V) : polyFun θ V (c • P) = c • polyFun θ V P := by
  funext g; simp [polyFun, MvPolynomial.smul_eval]

open Classical in
theorem envRepAll_ι_of (R : RealPoints θ V) (τ : D.what₂.Tau) (y : ℂ ⊗[ℝ] LieAt V τ) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ y)) =
      envRep R τ (UniversalEnvelopingAlgebra.ι ℂ y) := by
  rw [← envIncl_ι, envRepAll_envIncl]

theorem envRepAll_polyFun (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V) (P : PolyE V) :
    (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P) := by
  classical
  let S : Subalgebra ℂ (GlobalTheory.AutFinLit.Env V) :=
    { carrier := {u | ∀ P, (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P)}
      mul_mem' := fun {u v} hu hv P => by
        rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, ← hu]
        congr 2
        exact Subtype.ext (hv P)
      add_mem' := fun {u v} hu hv P => by
        rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hu, hv, polyFun_add]
      algebraMap_mem' := fun c P => by
        rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          Submodule.coe_smul, polyFun_smul] }
  have hι : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x ∈ S := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => rw [map_add (f := _), map_add (f := _)]; exact S.add_mem hy hy'
      | tmul c X =>
        intro P
        rw [envRepAll_ι_of, polyRep_ι_of, placeRep_tmul,
          show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
          map_smul, envRep_ι, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, opInf_coe,
          polyFun_smul, lieDer_polyFun D θ V R]
        rfl
  exact GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S hι u P

theorem realEntries_one (R : RealPoints θ V) :
    realEntries θ V 1 = fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0 := by
  funext p
  simp only [realEntries, R.2.2.2.2.1 1 (one_mem _) p.1, Matrix.one_apply]


set_option maxHeartbeats 1000000 in
open Classical in
theorem envRepAll_injective (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (_hθ : IsInfFam θ)
    (V : HSp D) (R : RealPoints θ V) : Function.Injective (envRepAll R) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  let ρ : ∀ τ, LieAt V τ → GlobalTheory.AutFinLit.Env V := fun τ X =>
    UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] X))
  have hadd : ∀ τ (X Y : LieAt V τ), ρ τ (X + Y) = ρ τ X + ρ τ Y := fun τ X Y => by
    simp only [ρ, TensorProduct.tmul_add, map_add (f := _)]
  have hsmul : ∀ τ (c : ℝ) (X : LieAt V τ), ρ τ (c • X) = (c : ℂ) • ρ τ X := fun τ c X => by
    have e1 : (1 : ℂ) ⊗ₜ[ℝ] (c • X) = (c : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Complex.real_smul, mul_one]
    simp only [ρ]
    rw [e1, ← DirectSum.lof_eq_of ℂ, map_smul, map_smul, DirectSum.lof_eq_of]
  have hbrk : ∀ τ (X Y Z : LieAt V τ), Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ τ Z = ρ τ X * ρ τ Y - ρ τ Y * ρ τ X :=
    fun τ X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      simp only [ρ]
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of_same, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  choose P Q hPQ hrest using fun τ =>
    GlobalTheory.UnitaryLieComplexification.glRel_and_span V.rank (gramAt D V τ) (R.1 τ).1 (R.1 τ).2
  have hgl := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).1
  have hsp := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).2
  let e : D.what₂.Tau × Fin V.rank × Fin V.rank → GlobalTheory.AutFinLit.Env V := fun p =>
    ρ p.1 (P p.1 p.2.1 p.2.2) + Complex.I • ρ p.1 (Q p.1 p.2.1 p.2.2)
  have hρe : ∀ τ X, ρ τ X ∈ Submodule.span ℂ (Set.range e) := fun τ X =>
    Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨(τ, p.1, p.2), rfl⟩) (hsp τ X)

  have hgen : Algebra.adjoin ℂ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 ((GlobalTheory.EnvCentre.adjoin_range_ι_eq_top _).symm.le.trans (Algebra.adjoin_le ?_))
    rintro _ ⟨x, rfl⟩
    refine Algebra.span_le_adjoin ℂ _ ?_
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add (f := _)]; exact add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hy'
      | tmul c X =>
        rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          ← DirectSum.lof_eq_of ℂ, map_smul, map_smul]
        exact Submodule.smul_mem _ c (hρe τ X)

  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ X Y, Commute (ρ τ X) (ρ τ' Y) := fun τ τ' h X Y => by
    have h1 : ρ τ X * ρ τ' Y - ρ τ' Y * ρ τ X = 0 := by
      simp only [ρ]; rw [← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of, dite_eq_right h, map_zero]
    exact sub_eq_zero.1 h1
  have hbr : ∀ p q, e p * e q - e q * e p ∈ Submodule.span ℂ (Set.range e) := by
    rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩
    by_cases h : τ = τ'
    · subst h
      have := hgl τ a b c d
      simp only at this
      change (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) * (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) -
        (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) * (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) ∈ _
      rw [this]
      refine sub_mem ?_ ?_
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, a, d), rfl⟩
        · exact zero_mem _
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, c, b), rfl⟩
        · exact zero_mem _
    · have hc : Commute (e (τ, a, b)) (e (τ', c, d)) := by
        simp only [e]
        refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
        · exact hcomm τ τ' h _ _
        · exact (hcomm τ τ' h _ _).smul_right _
        · exact (hcomm τ τ' h _ _).smul_left _
        · exact ((hcomm τ τ' h _ _).smul_left _).smul_right _
      rw [hc.eq, sub_self]; exact zero_mem _

  have hπρ : ∀ τ (X : LieAt V τ), polyRep V (ρ τ X) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := fun τ X => by
    simp only [ρ]; rw [polyRep_ι_of, placeRep_ι]
  have hE : ∀ τ a b, (P τ a b).1 + Complex.I • (Q τ a b).1 = Matrix.single a b (1 : ℂ) := fun τ a b => by
    rw [(hPQ τ a b).1, (hPQ τ a b).2, smul_smul]
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this]
    module
  have hπe : ∀ p, polyRep V (e p) = (matDer p.1 (Matrix.single p.2.1 p.2.2 (1 : ℂ)) : Module.End ℂ (PolyE V)) :=
    fun p => by
      simp only [e]
      rw [map_add (f := _), map_smul, hπρ, hπρ, ← hE, matDer_add, matDer_smul]
      rfl
  have hder : ∀ p (x y : PolyE V), polyRep V (e p) (x * y) = polyRep V (e p) x * y + x * polyRep V (e p) y :=
    fun p x y => by
      rw [hπe]
      change matDer _ _ (x * y) = matDer _ _ x * y + x * matDer _ _ y
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  let pt : D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ := fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0
  let χ : PolyE V →ₐ[ℂ] ℂ := MvPolynomial.aeval pt
  let a : D.what₂.Tau × Fin V.rank × Fin V.rank → PolyE V := fun p => MvPolynomial.X p - MvPolynomial.C (pt p)
  have ha0 : ∀ k, χ (a k) = 0 := fun k => by simp [χ, a]
  have hδ : ∀ i k, χ (polyRep V (e i) (a k)) = if i = k then 1 else 0 := by
    rintro ⟨τ, a', b'⟩ ⟨τ', c, d⟩
    rw [hπe]
    exact aeval_matDer_single τ τ' a' b' c d
  refine GlobalTheory.T.faithful_of_derivations_dualFamily _ _ _ e hgen hbr (polyRep V) hder χ a ha0 hδ u fun x => ?_
  have h1 := congrFun (envRepAll_polyFun R u x) 1
  rw [hu, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
  have h2 : polyFun θ V (polyRep V u x) 1 = χ (polyRep V u x) := by
    rw [polyFun, realEntries_one R, MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]; rfl
  rw [← h2, ← h1]

theorem exists_center {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} (hθ : IsInfFam θ)
    (R : RealPoints θ V) {z : List (ℝ → GA D V) →₀ ℂ} (hz : GlobalTheory.UAut.IsCentral D.sp.cm.sig V.gram z) :
    ∃ u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V), ∀ f : SmF θ V, GlobalTheory.UAut.dop z f.1 = (envRepAll R u f).1 := by
  obtain ⟨u, hu⟩ := exists_env hθ R z hz.1
  refine ⟨u, mem_center_of_comm u fun x => envRepAll_injective _ _ hθ V R ?_, hu⟩
  rw [map_mul, map_mul]
  refine GlobalTheory.EnvCommLie.envRepAll_comm_lie _ _ hθ V R u (fun a ha f hfa => ?_) x
  rw [← hu, ← hu]
  funext g
  exact hz.2 f.1 (isSm_of_smF hθ R f) a ha g

end GlobalTheory.CentralOps.Rg
end
end

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.CoreGL.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem exists_block {m : ℕ} (T : Finset (Fin m)) (k : Fin m) (hk : k ∈ T) :
    ∃ l d : ℕ, ∃ h : l + d ≤ m, 1 ≤ d ∧ k.val + 1 = l + d ∧ (∀ j : Fin m, l ≤ j.val → j.val + 1 < l + d → j ∉ T) ∧
      (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) := by
  classical
  by_cases hs : (T.filter (· < k)).Nonempty
  · set p := (T.filter (· < k)).max' hs with hp
    have hpm := Finset.mem_filter.1 ((T.filter (· < k)).max'_mem hs)
    have hpk : p.val < k.val := hpm.2
    refine ⟨p.val + 1, k.val - p.val, by have := k.2; omega, by omega, by omega, fun j h1 h2 hj => ?_, Or.inr ⟨p, hpm.1, rfl⟩⟩
    have hjk : j < k := by rw [Fin.lt_def]; omega
    have := (T.filter (· < k)).le_max' j (Finset.mem_filter.2 ⟨hj, hjk⟩)
    rw [← hp, Fin.le_def] at this
    omega
  · refine ⟨0, k.val + 1, by have := k.2; omega, by omega, by omega, fun j _ h2 hj => hs ⟨j, Finset.mem_filter.2 ⟨hj, ?_⟩⟩, Or.inl rfl⟩
    rw [Fin.lt_def]; omega

theorem levi_keeps {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {m : GAd σ J}
    (hm : m ∈ levi σ J X Y T) (k : Fin r) (hk : k ∈ T) (y : Fin n → AF F ⊗[F] E) :
    y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k} := by
  have fwd : ∀ m ∈ levi σ J X Y T, ∀ y, y ∈ colSpan F X {i | i ≤ k} → (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k} := by
    intro m hm y hy
    have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hm k) hk).1
    obtain ⟨B, -, e⟩ := h1
    obtain ⟨a, rfl⟩ := mem_colSpan_iff.1 hy
    refine mem_colSpan_iff.2 ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, mulVec_mulVec, e]
  refine ⟨fwd m hm y, fun h => ?_⟩
  have := fwd m⁻¹ (inv_mem hm) _ h
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

section Rep

variable {G K : Type} [Group G] [Group K]

def repOf (S : Submodule ℂ (K → ℂ)) (hS : ∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) (α : G →* K) : Representation ℂ G S where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (x * α g), hS f.1 f.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp
  map_mul' a b := by
    ext f x
    simp [mul_assoc]

theorem coeff_repOf (S : Submodule ℂ (K → ℂ)) (hS : ∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) (α : G →* K) {s : K → ℂ}
    (hs : s ∈ S) : (fun g => s (α g)) ∈ GlobalTheory.Published.AutFin.coeffSpan (repOf S hS α) :=
  Submodule.subset_span ⟨(LinearMap.proj (1 : K)).comp S.subtype, ⟨s, hs⟩, funext fun g => by
    change s (α g) = s (1 * α g)
    rw [one_mul]⟩

theorem isContRep_repOf [TopologicalSpace G] [TopologicalSpace K] [ContinuousMul K] (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (hS : ∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) (hc : ∀ f ∈ S, Continuous f) (α : G →* K)
    (hα : Continuous α) : IsContRep (repOf S hS α) := by
  classical
  intro ℓ w
  obtain ⟨P, hP⟩ := exists_finset_sep S
  let ev : S →ₗ[ℂ] (P → ℂ) :=
    { toFun := fun f p => f.1 p.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : LinearMap.ker ev = ⊥ := LinearMap.ker_eq_bot.2 ((injective_iff_map_eq_zero ev).2 fun f hf => Subtype.ext
    (hP f.1 f.2 fun x hx => congrFun hf ⟨x, hx⟩))
  obtain ⟨Lf, hL⟩ := LinearMap.exists_leftInverse_of_injective ev hinj
  have e : ∀ f : S, ℓ f = ∑ p : P, ℓ (Lf (Pi.single p 1)) * f.1 p.1 := fun f => by
    have h1 : f = Lf (ev f) := (LinearMap.congr_fun hL f).symm
    have h2 : ev f = ∑ p : P, f.1 p.1 • (Pi.single p 1 : P → ℂ) := by
      funext p
      simp [ev, Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [h1, h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  have : (fun g => ℓ (repOf S hS α g w)) = fun g => ∑ p : P, ℓ (Lf (Pi.single p 1)) * w.1 (p.1 * α g) := by
    funext g
    rw [e]
    rfl
  rw [this]
  exact continuous_finsetSum _ fun p _ => continuous_const.mul
    ((hc w.1 w.2).comp (continuous_const.mul hα))

theorem kfin_of_space {S : Submodule ℂ (K → ℂ)} [FiniteDimensional ℂ S] {H : Type} [Mul H] {i : K → H} {φ : H → ℂ}
    (h : ∀ g, (fun k => φ (g * i k)) ∈ S) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * i k))) := by
  let B := Module.finBasis ℂ S
  let c : Fin (Module.finrank ℂ S) → H → ℂ := fun a g => B.repr ⟨_, h g⟩ a
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have e : (fun g => φ (g * i k)) = ∑ a, (B a).1 k • c a := by
    funext g
    have h1 := congrFun (congrArg Subtype.val (B.sum_repr ⟨_, h g⟩)) k
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  change (fun g => φ (g * i k)) ∈ _
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Rep

section Centre

open PositivityTheory.Affgl GlobalTheory.CuspRep

theorem zfin_of_cofin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {J : Set (Module.End ℂ (Sm E a))}
    (hJ : Cofin J) {f : Sm E a} (hf : ∀ z ∈ J, z f = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z f) '' Zalg E a)) := by
  obtain ⟨-, V, hV, h⟩ := hJ
  let ev : Module.End ℂ (Sm E a) →ₗ[ℂ] Sm E a := LinearMap.applyₗ f
  have key : ∀ w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, w f = 0 := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, -, j, hj, rfl⟩ := hx
      rw [Module.End.mul_apply, hf j hj, map_zero]
    | zero => rfl
    | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
    | smul a x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
  refine Submodule.finiteDimensional_of_le (S₂ := V.map ev) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨v, hv, w, hw, e⟩ := Submodule.mem_sup.1 (h z hz)
  refine ⟨v, hv, ?_⟩
  change v f = z f
  rw [← e, LinearMap.add_apply, key w hw, add_zero]

end Centre

section Gelf

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem zfin_of_gelf (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : IsSm D.sp.cm.sig V.gram φ) {c : D.what₂.Tau → ℕ → ℂ}
    (hg : ∀ τ k, gelf θ V τ k φ = c τ k • φ) :
    FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral D.sp.cm.sig V.gram z ∧ f = dop z φ}) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hW : ∀ τ k, ∀ f ∈ Submodule.span ℂ {φ}, gelf θ V τ k f ∈ Submodule.span ℂ {φ} := by
    intro τ k f hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
    rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, hg, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨u, hu, e⟩ := GlobalTheory.CentralOps.Rg.exists_center hθ R hz
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 fun k τs Xs hX g =>
    hs k (fun i => oneP θ V (τs i) (Xs i)) (fun i => GlobalTheory.T.unitary_lie_one_parameter_isRealOneParamSubgroupAdelic D θ hθ V _ _ (hX i)) g⟩
  exact (e ψ).symm ▸ GlobalTheory.CentralOps.mem_of_mem_center R hW hu ψ (Submodule.mem_span_singleton_self φ)

end Gelf

section Main


open GlobalTheory.CuspRep in
theorem finite_slices_glPart : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∀ k ∈ T, ∀ b : GA D V, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (glPart D.sp.cm.sig V.gram X Y T k) (levi D.sp.cm.sig V.gram X Y T) b)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hW T hT k hk b
  classical
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).1
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).2 V
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  haveI : IsTotallyComplex D.host.E := inferInstance
  obtain ⟨l, d, hl, hd, hkl, hblk, hprev⟩ := exists_block T k hk
  have hend : ∃ k' ∈ T, k'.val + 1 = l + d := ⟨k, hk, hkl⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.BlockFormsEmb.exists_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW l d hl
  have hrange := GlobalTheory.T.block_embedding_parabolic_compatibility _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T k hk l d hl ι hι hkl hd hblk hprev
  have hιH : ∀ x, ι x ∈ glPart D.sp.cm.sig V.gram X Y T k := fun x => hrange ▸ ⟨x, rfl⟩
  obtain ⟨K, hKm, j, hjs, hj⟩ := GlobalTheory.T.exists_maxCompact_realPoints_of_orthonormalFrames D θ hθ V ε fr hfr
  have hK : IsMaxCpt D.sp.cm.sig V.gram K :=
    ⟨⟨fun x hx => hKm.1 x hx, hKm.2.1⟩, fun K' hK' hle => (hKm.2.2 K' (fun x hx => hK'.1 hx) hK'.2 hle).le⟩
  obtain ⟨u, hu, -, y₁, g₀, hb, hg₀⟩ := GlobalTheory.T.parabolic_block_embedding_compact _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev b
  obtain ⟨S, hSf, hSc, hSt, hSφ⟩ := GlobalTheory.typesFiniteSpace D θ hθ V ε fr hfr K ⟨j, hjs, hj⟩ W ρ
  haveI := hSf
  let α : Kinf D.host.E d →* K :=
    { toFun := fun κ => ⟨g₀⁻¹ * ι (infGL D.host.E d (Unitary.toUnits κ)) * g₀, hg₀ κ⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hιc := GlobalTheory.BlockLevel.continuous_of_isBlockEmb hι
  have hα : Continuous α := Continuous.subtype_mk
    ((continuous_const.mul (hιc.comp CompanionTheory.D.gk.Br.LIC.continuous_infGL_toUnits)).mul continuous_const) _
  let ρ' := repOf S hSt α
  have hρ' : IsContRep ρ' := isContRep_repOf S hSt hSc α hα
  let L : Subgroup (GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E)) :=
    U.comap ((MulAut.conj g₀⁻¹).toMonoidHom.comp (ι.comp (finGL D.host.E d)))
  have hL : IsOpen (L : Set (GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E))) := by
    refine hU.preimage ?_
    have : Continuous fun k : GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E) => g₀⁻¹ * ι (finGL D.host.E d k) * g₀⁻¹⁻¹ :=
      (continuous_const.mul (hιc.comp CompanionTheory.D.gk.Br.LIC.continuous_finGL)).mul continuous_const
    exact this
  choose q hq hq0 using GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock.monic_block D θ hθ V c m X Y hW T l d hl ι hι hd hblk hend hprev
  let Js : Set (Module.End ℂ (Sm D.host.E d)) :=
    Set.range fun p : (D.host.E →+* ℂ) × ℂ => Polynomial.aeval (cap (a := d) p.1 p.2) (q p.1 p.2)
  have hJs : Js ⊆ Zalg D.host.E d := by
    rintro _ ⟨p, rfl⟩
    have h : cap (a := d) p.1 p.2 ∈ Zalg D.host.E d := Algebra.subset_adjoin ⟨p.1, p.2, rfl⟩
    change Polynomial.aeval _ _ ∈ Zalg D.host.E d
    rw [Polynomial.aeval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (pow_mem h i) _
  have hCof := GlobalTheory.T.cofinite_of_capelli_monic D.host.E d Js hJs fun τ v => ⟨q τ v, hq τ v, ⟨(τ, v), rfl⟩⟩
  have hfin := GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFin D.host.E d L hL S ρ' hρ' Js hCof
  have hnorm : (finPts D.sp.cm.sig V.gram).Normal := by
    unfold finPts
    infer_instance
  have key : ∀ φ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y : GA D V,
      (∀ t ∈ glPart D.sp.cm.sig V.gram X Y T k, t * y = y * t) →
      ∃ F : Sm D.host.E d, (∀ x, F.1 x = φ (ι x * (y * g₀))) ∧
        F ∈ {F | F ∈ PositivityTheory.Affgl.genSpace L ρ' Js ∧ IsCuspidal F.1} := by
    intro φ hφ y hy
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hφ
    have hc : GlobalTheory.StdPar.IsCuspOn D.sp.cm.sig V.gram X Y T K φ :=
      ⟨⟨fun u hu g => h1.left u (Subgroup.mem_sup_left hu) g,
        fun γ a b g => h1.left γ (Subgroup.mem_sup_right ⟨a, b⟩) g, h1.level, h1.cont, h1.smooth, h1.growth,
        kfin_of_space (S := S) (i := Subtype.val) (hSφ φ h1.cont h3), zfin_of_gelf hθ h1.smooth h4⟩, h5⟩
    have hcj : ∀ x, (y * g₀)⁻¹ * ι x * (y * g₀) = g₀⁻¹ * ι x * g₀ := fun x => by
      have e := hy (ι x) (hιH x)
      calc (y * g₀)⁻¹ * ι x * (y * g₀) = g₀⁻¹ * y⁻¹ * (ι x * y) * g₀ := by group
        _ = g₀⁻¹ * ι x * g₀ := by rw [e]; group
    have hg₁ : ∀ κ : Kinf D.host.E d, (y * g₀)⁻¹ * ι (infGL D.host.E d (Unitary.toUnits κ)) * (y * g₀) ∈ K := fun κ => by
      rw [hcj]; exact hg₀ κ
    have hmv : ∀ x a, ι (x * a) * (y * g₀) = ι x * (y * g₀) * (g₀⁻¹ * ι a * g₀) := fun x a => by
      rw [← hcj, map_mul]; group
    let F : Sm D.host.E d := ⟨fun x => φ (ι x * (y * g₀)), GlobalTheory.CuspSmooth.mem_Sm_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁⟩
    have hkill : ∀ z ∈ Js, z F = 0 := by
      rintro _ ⟨p, rfl⟩
      exact hq0 p.1 p.2 φ h1 h4 _ F fun _ => rfl
    have hlev : ∀ a ∈ L, finRep D.host.E d a F = F := by
      intro a ha
      refine Subtype.ext (funext fun x => ?_)
      change φ (ι (x * finGL D.host.E d a) * (y * g₀)) = φ (ι x * (y * g₀))
      have hU' : g₀⁻¹ * ι (finGL D.host.E d a) * g₀ ∈ U := by simpa [L, MulAut.conj_apply] using ha
      have hf' : g₀⁻¹ * ι (finGL D.host.E d a) * g₀ ∈ finPts D.sp.cm.sig V.gram := by
        simpa using hnorm.conj_mem _ (GlobalTheory.BlockLevel.finGL_mem_finPts hι a) g₀⁻¹
      rw [hmv]
      exact h2 _ hU' hf' _
    have hcoef : ∀ g : GlobalTheory.CuspRep.GA D.host.E d, (fun κ : Kinf D.host.E d => (cptRep D.host.E d κ F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ' := by
      intro g
      have e : (fun κ : Kinf D.host.E d => (cptRep D.host.E d κ F).1 g) =
          fun κ => (fun k : K => φ (ι g * (y * g₀) * k)) (α κ) := funext fun κ => by
        change φ (ι (g * infGL D.host.E d (Unitary.toUnits κ)) * (y * g₀)) = _
        rw [hmv]
        rfl
      rw [e]
      exact coeff_repOf S hSt α (hSφ φ h1.cont h3 _)
    have haut : IsAutForm F := by
      refine ⟨GlobalTheory.CuspBlockLeft.cuspForm_blockEmb_left_invariant _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁, ?_, ?_, zfin_of_cofin hCof hkill, GlobalTheory.BlockForms.growth_comp_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁⟩
      · have e : {a | finRep D.host.E d a F = F} = {a : GL (Fin d) (GlobalTheory.CuspRep.Af D.host.E) | ∀ g, φ (ι (g * finGL D.host.E d a) * (y * g₀)) = φ (ι g * (y * g₀))} :=
          Set.ext fun a => ⟨fun e g => congrFun (congrArg Subtype.val e) g, fun e => Subtype.ext (funext e)⟩
        rw [e]
        exact GlobalTheory.BlockLevel.isOpen_rightInv_finGL _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁
      · have e : (Submodule.span ℂ (Set.range fun a => cptRep D.host.E d a F)).map (Sm D.host.E d).subtype =
            Submodule.span ℂ (Set.range fun a : Kinf D.host.E d => fun g : GlobalTheory.CuspRep.GA D.host.E d => φ (ι (g * infGL D.host.E d (Unitary.toUnits a)) * (y * g₀))) := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        have := GlobalTheory.CuspKinfFin.kinf_finite _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁
        rw [← e] at this
        exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective (Sm D.host.E d).subtype Subtype.val_injective
          (Submodule.span ℂ (Set.range fun a => cptRep D.host.E d a F))).symm
    exact ⟨F, fun _ => rfl, ⟨haut, hlev, hcoef, hkill⟩,
      GlobalTheory.BlockForms.CuspConst.Rg.isCuspidal_comp_blockEmb _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW K hK T l d hl ι hι hd hblk hend hprev φ hc _ hg₁⟩
  have hmem : ∀ t : glPart D.sp.cm.sig V.gram X Y T k, t.1 ∈ ι.range := fun t => hrange ▸ t.2
  let pre : glPart D.sp.cm.sig V.gram X Y T k → GlobalTheory.CuspRep.GA D.host.E d := fun t => Classical.choose (hmem t)
  have hpre : ∀ t, ι (pre t) = t.1 := fun t => Classical.choose_spec (hmem t)
  let Λ : Sm D.host.E d →ₗ[ℂ] (glPart D.sp.cm.sig V.gram X Y T k → ℂ) :=
    { toFun := fun F t => F.1 (pre t * infGL D.host.E d y₁)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI := hfin
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ {F | F ∈ PositivityTheory.Affgl.genSpace L ρ' Js ∧ IsCuspidal F.1}).map Λ) (Submodule.span_le.2 ?_)
  rintro f ⟨φ, hφ, y, hy, hyc, rfl⟩
  obtain ⟨F, hF, hFm⟩ := key φ hφ y hyc
  refine ⟨F, Submodule.subset_span hFm, funext fun t => ?_⟩
  change F.1 (pre t * infGL D.host.E d y₁) = φ (t.1 * y * b)
  rw [hF, map_mul, hpre, hb]
  have hy1 := hyc _ (hιH (infGL D.host.E d y₁))
  have hty : t.1 * y ∈ levi D.sp.cm.sig V.gram X Y T := mul_mem t.2.1 hy
  have hu' := GlobalTheory.FlagNorm.conj_mem_unip _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T (t.1 * y)
    (fun k' hk' v => levi_keeps hty k' hk' v) u hu
  have e1 : t.1 * ι (infGL D.host.E d y₁) * (y * g₀) = t.1 * y * ι (infGL D.host.E d y₁) * g₀ := by
    rw [mul_assoc t.1, ← mul_assoc (ι _), hy1]
    simp only [mul_assoc]
  have e2 : t.1 * y * (u * ι (infGL D.host.E d y₁) * g₀) =
      (t.1 * y * u * (t.1 * y)⁻¹) * (t.1 * ι (infGL D.host.E d y₁) * (y * g₀)) := by
    rw [e1]; group
  rw [e2]
  exact (hφ.1.1.left _ (Subgroup.mem_sup_left hu') _).symm

end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.CoreGL.Rg
