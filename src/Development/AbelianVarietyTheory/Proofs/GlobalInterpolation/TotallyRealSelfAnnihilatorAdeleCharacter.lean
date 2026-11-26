module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.Annihilator

variable {F : Type} [Field F] [NumberField F]

private theorem ext_lemma {x y : AF F} (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) :
    x = y :=
  Prod.ext h1 h2

private theorem mul_pairA_zero (x : AF F) (z : Ainf F) :
    x * pairA F z 0 = pairA F (fstA F x * z) 0 := by
  apply ext_lemma
  · rw [map_mul]
    rfl
  · rw [map_mul]
    show sndA F x * 0 = 0
    exact mul_zero _

private theorem mul_pairA_singleV (x : AF F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    x * pairA F 0 (singleV F v t) = pairA F 0 (singleV F v (sndA F x v * t)) := by
  apply ext_lemma
  · rw [map_mul]
    show fstA F x * 0 = 0
    exact mul_zero _
  · rw [map_mul]
    show sndA F x * singleV F v t = singleV F v (sndA F x v * t)
    unfold singleV
    classical
    exact (RestrictedProduct.mul_single _ v t (sndA F x)).symm

theorem eq_zero_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨hloc, -, hinf⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  apply ext_lemma
  ·
    have h0 : fstA F x = 0 := hinf _ fun y => by
      have h := hx (pairA F y 0)
      rw [mul_pairA_zero] at h
      exact h
    rw [h0, map_zero]
  ·
    have key : ∀ v, sndA F x v = 0 := by
      intro v
      by_contra hne
      obtain ⟨s, hs⟩ := hloc v
      apply hs
      have h := hx (pairA F 0 (singleV F v ((sndA F x v)⁻¹ * s)))
      rw [mul_pairA_singleV, mul_inv_cancel_left₀ hne] at h
      exact h
    rw [map_zero]
    exact DFunLike.ext _ _ fun v => (key v).trans rfl

theorem exists_eq_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) : ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  by_cases htriv : ∀ y, ψ (x * y) = 1
  · exact ⟨0, by rw [map_zero]; exact eq_zero_of_forall hψ x htriv⟩
  · push_neg at htriv
    obtain ⟨hc, hn, -, -⟩ := id hψ

    have hχ : IsCharAF F (ψ.compAddMonoidHom (AddMonoidHom.mulLeft x)) := by
      unfold IsCharAF
      exact ⟨hc.comp (continuous_const.mul continuous_id), fun y => hn _, hx, htriv⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ _ hψ hχ
    refine ⟨a, sub_eq_zero.mp (eq_zero_of_forall hψ _ fun y => ?_)⟩
    have h1 : ψ (x * y) = ψ (algebraMap F (AF F) a * y) := ha y
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]

theorem self_annihilator : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∀ x : AF F, (∀ y, ψ (x * y) = 1) → x = 0) ∧ ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  intro F _ _ hF ψ hψ
  haveI := hF
  exact ⟨fun x hx => eq_zero_of_forall hψ x hx, fun x hx => exists_eq_of_forall hψ x hx⟩

end GlobalTheory.SWQ.Annihilator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numberField_self_annihilator_adeleCharacter : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∀ x : AF F, (∀ y, ψ (x * y) = 1) → x = 0) ∧ ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  first | exact @GlobalTheory.SWQ.Annihilator.self_annihilator | exact GlobalTheory.SWQ.Annihilator.self_annihilator | (intros; apply GlobalTheory.SWQ.Annihilator.self_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.LamExists

theorem re_mul_of_isReal {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (a : F) (x : Ainf F)
    (w : InfinitePlace F) : re (algebraMap F (Ainf F) a * x) w = re (algebraMap F (Ainf F) a) w * re x w := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  show (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w * x w)).re = _
  rw [map_mul, Complex.mul_re, hr, zero_mul, sub_zero]
  rfl

theorem re_ne_zero {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) (w : InfinitePlace F)
    (hF : IsTotallyReal F) : re (algebraMap F (Ainf F) a) w ≠ 0 := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  intro h0
  have : InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w) = 0 :=
    Complex.ext h0 hr
  rw [InfiniteAdeleRing.algebraMap_apply] at this
  rw [InfinitePlace.Completion.extensionEmbedding_coe, map_eq_zero] at this
  exact ha this

end GlobalTheory.SWQ.LamExists

theorem GlobalTheory.SWQ.exists_isLam : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ lam, IsLam ψ lam := by
  intro F _ _ hF ψ hψ
  haveI := hF
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 hψ
  refine ⟨fun w => re (algebraMap F (Ainf F) a) w, fun w => GlobalTheory.SWQ.LamExists.re_ne_zero a ha w hF, fun x => ?_⟩
  rw [GlobalTheory.GaugeEx.CharLoc.psiInf_twist h, h₀.2.1]
  exact congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => GlobalTheory.SWQ.LamExists.re_mul_of_isReal hF a x w)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_exponents_adeleCharacter : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ lam, IsLam ψ lam := by
  first | exact @GlobalTheory.SWQ.exists_isLam | exact GlobalTheory.SWQ.exists_isLam | (intros; apply GlobalTheory.SWQ.exists_isLam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMass
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMass
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassRestObj

theorem defClassRest : ∀ D : D7, DefClassRest D := by
  intro D W hW hsig
  obtain ⟨⟨θ, hθ⟩, A, hA⟩ := GlobalTheory.DecompCompare.exists_data D W hW hsig
  have hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W) :=
    SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)
  obtain ⟨-, n, g, hcov, hdisj, -, hsum⟩ := GlobalTheory.DefiniteDecompObj.doubleCosets_mass D W hW hsig θ hθ A hA
  rw [hK] at hcov hdisj hsum
  exact ⟨n, g, hcov, hdisj, hsum⟩

end GlobalTheory.ClassRestObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMassStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass : ∀ D : D7, DefClassRest D := by
  first | exact @GlobalTheory.ClassRestObj.defClassRest | exact GlobalTheory.ClassRestObj.defClassRest | (intros; apply GlobalTheory.ClassRestObj.defClassRest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndep
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndep
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volMeas_fundDomain_eq_of_tiedIndep :
    (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  intro H D W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr μ 𝓕 μ₀ 𝓕₀ hμ h𝓕 hμ₀ h𝓕₀
  have hT : VolTie (GlobalTheory.Mem.retie D) :=
    Formalism.L2.Theta.VolTieG.volTie (GlobalTheory.Mem.retie_volTieG_and_cdScaleTie D).1
  have e1 : μ 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W) :=
    ((hT W P Q hW hs).2 μ hμ).2 𝓕 h𝓕
  have e2 : μ₀ 𝓕₀ = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W₀) :=
    ((hT W₀ P₀ Q₀ hW₀ hs₀).2 μ₀ hμ₀).2 𝓕₀ h𝓕₀
  rw [e1, e2, H (GlobalTheory.Mem.retie D) hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr]

end GlobalTheory.Glob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndepStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep : (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  first | exact @GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | exact GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | (intros; apply GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdicIntegersCharacterDualIndexEqResidueCardZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdicIntegersCharacterDualIndexEqResidueCardZpow
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.DualIndexPow

theorem nIdx_eq_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  intro F _ _ ψ v c h
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-c))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  have hu : ∀ hx : WithZero.exp (-c) ≠ 0, Multiplicative.toAdd (WithZero.unzero hx) = -c :=
    fun _ => rfl

  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.psiDual F ψ v = GlobalTheory.LocalDensityProduct.colonV v a := by
    ext t
    rw [GlobalTheory.LocalDensityProduct.mem_colonV]
    change (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ _
    rw [h t, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, ha,
      WithZero.exp_neg, mul_inv_le_iff₀ (by simp), one_mul]
  have hi : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.intV F v = GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.intV F v := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.nIdx
  rw [hd, hi, (GlobalTheory.LocalDensityProduct.index_colonV v a ha0).2,
    NumberField.FinitePlace.norm_def, ha,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard]
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, WithZero.log_exp]
  simp [_root_.zpow_neg]

end GlobalTheory.DualIndexPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdicIntegersCharacterDualIndexEqResidueCardZpowStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegersCharacterDualIndex_eq_residue_card_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  first | exact @GlobalTheory.DualIndexPow.nIdx_eq_zpow | exact GlobalTheory.DualIndexPow.nIdx_eq_zpow | (intros; apply GlobalTheory.DualIndexPow.nIdx_eq_zpow <;> assumption)
end
end
