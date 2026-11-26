module

public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLevelTranslatedEvaluationOfConjRow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationGoodRowsToConjugateGoodRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Chi2ApplyOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolFormalDegreeEq
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem covol_formalDegree_eq : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D →
    Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ :=
  fun _D X h hVol hcd hT => Formalism.L2.SG.Pf.DstarVolPf.dstarVol_holds X h hVol hcd hT

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DEqFinrankHHX
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsCount


open Formalism _root_.Formalism.L2 _root_.Formalism.L2.SG in
theorem projRowsR : Formalism.L2.SG.ProjRows.ProjRowsR :=
  Formalism.L2.SG.ProjRows.projRowsR_of schur_orthogonality_idempotent convolution_projection isConvIdempotent_pi
    Formalism.L2.SG.Pf.regular_representation_unitary


open Formalism _root_.Formalism.L2 _root_.Formalism.L2.SG in
theorem unimodGf : Formalism.L2.SG.Pf.UnimodGf := fun I μf _ _ =>
  (PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable
    PI.adelic_index_eq) I μf inferInstance

theorem D_eq_finrank_HHX : ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → X.B.D = Module.finrank ℂ (HHX X) := by
  intro D X h
  exact (Formalism.L2.SG.RowsDef.RowsAut.D_eq_finrank_HH (Formalism.L2.SG.Pf.rows_bijective projRowsR unimodGf) X.B _
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec).1

end GlobalTheory.RowsCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FEqAndRdEq
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace GlobalTheory.DegreeRankEquations

theorem f_eq (D : D7) (X : HidaSetting D) : X.B.I.f = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  unfold AutInst.f
  omega

theorem rd_eq (D : D7) (X : HidaSetting D) : X.B.I.rd = D.host.rdE := by
  have hd : discr X.B.I.E = discr D.host.E := NumberField.discr_eq_discr_of_algEquiv X.B.I.E X.ιE.toRatAlgEquiv
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : (Module.finrank ℚ D.host.E : ℝ) = 2 * (X.B.I.f : ℝ) := by
    unfold AutInst.f
    have : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ X.B.I.F := by rw [← e1, ← e2, e3, mul_comm]
    rw [this]; push_cast; ring
  unfold AutInst.rd Host.rdE
  rw [hd, e4]

end GlobalTheory.DegreeRankEquations
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.BundleTie

variable {D : D7} (X : HidaSetting D)

theorem chi2_apply_one : X.chi2 1 = 1 := by

  obtain ⟨h1, -, -, hmul, hnorm⟩ := Formalism.L2.SG.Pf.level_subgroup_character_unitary X
  have hsq := hmul 1 h1 1 h1
  rw [mul_one (1 : X.B.I.Gf)] at hsq
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have hn := hnorm 1 h1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact hsq.symm)

theorem e_one : X.B.e 1 = 1 / (X.volK2 : ℂ) := by
  have h1 : (1 : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := (Formalism.L2.SG.Pf.level_subgroup_character_unitary X).1
  rw [X.e_eq 1, if_pos h1]
  have hc : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd 1 = 1 := chi2_apply_one X
  rw [hc, star_one]
  rfl


open Formalism _root_.Formalism.L2 _root_.Formalism.L2.SG in
theorem dstarD_eq
    (hI : (X.B.μf X.B.I.Kset).toReal / X.volK2 = Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1))
    (hV : (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) :
    Formalism.MainNotions.StandardLattice.DstarD D =
      X.B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.μf X.B.fund X.B.e := by
  have hre : (X.B.e 1).re = 1 / X.volK2 := by
    rw [e_one X, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hd : (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) = ∏ v, X.dv v := rfl
  have hsub : X.K2 ⊆ X.B.I.Kset := fun x hx => hx.1
  have hv2 : X.volK2 = (X.B.μf X.K2).toReal := rfl
  show Formalism.MainNotions.StandardLattice.volY0 D * Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ ρ, D.dsig ρ =
    (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) * X.B.I.vol X.B.μf X.B.fund * (X.B.e 1).re
  rw [hre, hd, ← hI]
  by_cases hv : X.volK2 = 0
  · rw [hv]
    simp
  ·
    have hK2 : X.B.μf X.K2 ≠ 0 := by
      intro h
      apply hv
      simp [hv2, h]
    have hμ : (X.B.μf X.B.I.Kset).toReal ≠ 0 := by
      rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨fun h => hK2 (measure_mono_null hsub h),
        (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top.ne⟩
    calc Formalism.MainNotions.StandardLattice.volY0 D * ((X.B.μf X.B.I.Kset).toReal / X.volK2) * ∏ ρ, D.dsig ρ
        = (Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) * (X.B.μf X.B.I.Kset).toReal / X.volK2 := by ring
      _ = ((∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal) *
            (X.B.μf X.B.I.Kset).toReal / X.volK2 := by rw [hV]
      _ = (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund * (1 / X.volK2) := by
        rw [div_mul_cancel₀ _ hμ, mul_one_div]

theorem autTie : ∀ (D : D7) (X : HidaSetting D), Nonempty (D.s.HH ≃ₗᵢ[ℂ] HHX X) →
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → D.what₂.Dstar = Formalism.MainNotions.StandardLattice.DstarD D →
    X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    AutTie D X.B X.pl := by
  intro D X hHH hint hD hinst hVol hcd hds
  obtain ⟨ι⟩ := hHH
  have hV := GlobalTheory.covol_formalDegree_eq D X hinst hVol hcd hds
  have hI := Formalism.L2.SG.Pf.DstarIdxPf.dstarIdx_holds X
  exact
    { n_eq := X.n_eq
      f_eq := GlobalTheory.DegreeRankEquations.f_eq D X
      rd_eq := GlobalTheory.DegreeRankEquations.rd_eq D X
      eps_eq := X.eps_eq
      lam_eq := X.lam_eq
      ds := X.ds
      low := X.low
      g_eq := X.g_eq
      g0_eq := X.g0_eq
      D_eq := by
        rw [GlobalTheory.RowsCount.D_eq_finrank_HHX D X hint, ← ι.toLinearEquiv.finrank_eq, D.s_HH]
      Dstar_eq := hD.trans (dstarD_eq X hI hV) }

end GlobalTheory.BundleTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStages
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSRestRe
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealReS
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem real_reS : ∀ (D : D7) (Z : SNew D), (Formalism.L2.Theta.RealTied D → Formalism.L2.Theta.RealTied (reS D Z)) ∧ StandardLattice.DstarD (reS D Z) = StandardLattice.DstarD D ∧ (StandardLattice.VolumeEqMass₂ D → StandardLattice.VolumeEqMass₂ (reS D Z)) :=
  fun _ _ => ⟨fun h => ⟨h.cdScale, h.dsig, h.dsig_all, h.vol⟩, rfl, fun h => h⟩

end GlobalTheory.Mem.SRe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CdScaleEqCdScaleOf
open Formalism.BasicNotions

namespace GlobalTheory.Mem.SRe

theorem cdScale_eq_cdScaleOf : ∀ D : D7, cdScaleTie D → D.s.cdScale = Formalism.L2.SG.PairVal.cdScaleOf D := by
  intro D h
  exact GlobalTheory.Mem.Vol.Scale.cdScaleIs_unique D.cd ((GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 h)
    (fun n ε => (Formalism.L2.SG.PairVal.cdScaleOf_tie D (Formalism.L2.SG.PairVal.cdScaleExists_of_tie D h) n ε).2)

end GlobalTheory.Mem.SRe
end

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

section Core

variable {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
  (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)
  (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y))


set_option maxHeartbeats 4000000 in
def sIsoRe (hR : Formalism.L2.Theta.RealTied D) (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) :
    SIso (reD D ⟨P.toNew hD j, N, hh⟩).s (sOf hF) where
  cd := by
    have h := (real_reS D (P.toNew hD j)).1 hR
    exact cdScale_eq_cdScaleOf (reD D ⟨P.toNew hD j, N, hh⟩) ((by with_unfolding_all exact (h.cdScale :)))
  del := rfl
  letter := rfl
  eHH := (by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))
  eCu := fun u => (by with_unfolding_all exact (eCure ⟨P.toNew hD j, N, hh⟩ P.fin hF u :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).1 :))
  volN := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).1 :))
  volH := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).2 :))
  eT := fun u u' => (by with_unfolding_all exact (eRT ⟨P.toNew hD j, N, hh⟩ P.Y u u' :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => by
    apply Subtype.ext
    exact (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.1 :))
  atP := fun p => (by with_unfolding_all exact ((hL p).some :))
  ePl := (by with_unfolding_all exact (Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.1 q :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.1 :))
  eP := fun u u' => (by with_unfolding_all exact ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose :))
  pfst := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1 :))
  psnd := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.1 :))
  s0 := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.1 :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.1 :))
  pval := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.2 :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} (p : RP P.Y u u') => by
    have h1 := ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 p.1.1).2.2.2.2.2.2.2.2.1
    have h2 := ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1
    exact (by with_unfolding_all exact (h1.trans (congrArg (fun t => Formalism.L2.SG.PairVal.massTerm t) h2) :))
  meanCount := by
    funext u u' w
    exact (by with_unfolding_all exact ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').2 w :))

end Core

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem exists_sRest_re : ∀ (D : D7) (F : ∀ u, Forms0 D u) (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F F') (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)), Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.Theta.RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → ∃ S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro D F P hD j N hh F' hs hF hph hL hR hDs
  have hR' := (real_reS D (P.toNew hD j)).1 hR
  have hDs' : (reD D ⟨P.toNew hD j, N, hh⟩).what₂.Dstar = StandardLattice.DstarD (reD D ⟨P.toNew hD j, N, hh⟩) := (by with_unfolding_all exact (hDs.trans (real_reS D (P.toNew hD j)).2.1.symm :))
  have hAut : Formalism.MainNotions.S.AutTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.B
      (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.pl :=
    GlobalTheory.BundleTie.autTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X
      ⟨(by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))⟩ ((by with_unfolding_all exact (hph :))) hDs' (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).inst
      ((by with_unfolding_all exact (Formalism.L2.Theta.VolTieG.volTie hR'.vol :))) ((by with_unfolding_all exact (hR'.cdScale :))) ((by with_unfolding_all exact (hR'.dsig_all :)))
  refine ⟨⟨sIsoRe P hD j N hh hF hR hL, hAut, ?_, j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G), ?_, (by with_unfolding_all exact (hL :))⟩, rfl⟩
  · intro u x
    apply Subtype.ext
    exact (by with_unfolding_all exact (colDictL_reTr ⟨P.toNew hD j, N, hh⟩ (P.tr u) (hs u).2.1 (hs u).2.2 P.Y.hK x :))
  · intro x
    exact (by with_unfolding_all exact ((conjHH_eEECre ⟨P.toNew hD j, N, hh⟩ P.G (j x)).symm :))

end GlobalTheory.Mem.SRe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjTranslatedLevelRowEvaluationMemAllRows
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjTranslatedLevelRowEvaluationMemAllRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace


open GlobalTheory.Core.Mi GlobalTheory.Core.Mi.SeeHH in
theorem GlobalTheory.Mem.SRe.conj_ev_mem_HHX : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ MultR R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → star φ ∈ HHX X := by
  intro hDS hP hUq hRF D G' _ _ Pl0 T A Ks _ _ _ R F X h t hIdE hG hLev hinf hν hSee c v₀ hc1 hc2 S hS φ hφ
  have hθ : IsInfFam R.θ := hinf
  have hMat : Matches X h (JR R F) (chiR R F) t := ⟨hSee.fin, hSee.conj⟩
  have hCV : ConjVec X h R.θ (MP R) v₀ := ⟨c, hc1, hc2⟩
  have hL : ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v))
      (Formalism.REAL.muG (X.B.I.ε v)) := fun v => by
    have h1 := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
      (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond hG) v
    have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
      h1.mono (continuous_star.comp_aestronglyMeasurable h1.1) (ae_of_all _ fun g => le_of_eq (norm_star _))
    exact hs.const_mul ((X.dv v : ℝ) : ℂ)
  have hR := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h R.θ hθ hIdE
  have hT : PiTensorProduct.lift S ∈ MultT R.θ (MP R) (JR R F) (chiR R F) := by
    refine (mem_multT R.θ (MP R) (JR R F) (chiR R F) _).2 ?_
    rw [LinearEquiv.symm_apply_apply]; exact hS
  obtain ⟨hRow, hMem⟩ := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hP D X h R.θ _ (MP R) (JR R F) (chiR R F) t hθ hMat _ hT
    (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) x =
      S v₀ ((iotaX X h).symm x * t) := fun x => by
    delta evS
    rw [PiTensorProduct.lift.tprod]
  generalize evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hfx
  have hφ2 : (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f := hφ.trans (Filter.Eventually.of_forall fun x => (hfx x).symm)
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ2.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge (MP R) R.θ (JR R F) (chiR R F)
    (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t S hS S hS
  have hv₀ : ∏ τ, ⟪(v₀ τ : (MP R).H τ), (v₀ τ : (MP R).H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : (MP R).H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h R.θ (MP R) (JR R F) (chiR R F) t hMat.1 hR v₀ g
    have hco := coef_eq X h R.θ (MP R) v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (S w ((iotaX X h).symm x * t)) * S v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh S hS x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjTranslatedLevelRowEvaluationMemAllRowsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_translated_level_row_evaluation_mem_all_rows : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ MultR R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → star φ ∈ HHX X := by
  exact @GlobalTheory.Mem.SRe.conj_ev_mem_HHX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRows
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.EvalAllRows

theorem eq_zero_of_units {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T : MMap M)
    (h : ∀ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) → T v = 0) : T = 0 := by
  classical
  refine MultilinearMap.ext fun v => ?_
  by_cases hz : ∃ τ, v τ = 0
  · obtain ⟨τ, hτ⟩ := hz
    exact T.map_coord_zero τ hτ
  · push_neg at hz
    have hn : ∀ τ, ‖(v τ : M.H τ)‖ ≠ 0 := fun τ e => hz τ (Subtype.ext (norm_eq_zero.1 e))
    let u : M.Vec := fun τ => ((‖(v τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • v τ
    have hu : ∀ τ, ‖(u τ : M.H τ)‖ = 1 := fun τ => by
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hn τ)
    have hv : v = fun τ => ((‖(v τ : M.H τ)‖ : ℝ) : ℂ) • u τ := by
      funext τ
      simp only [u, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hn τ), Complex.ofReal_one, one_smul]
    rw [hv, T.map_smul_univ, h u hu, smul_zero]
    rfl

end GlobalTheory.EvalAllRows

theorem GlobalTheory.EvalAllRows.evalTranslate_norm_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro _ hCusp _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hHE hGap hL hinf hν0 hsee
  haveI hνH : R.ν0.IsHaarMeasure := hν0.1.1
  obtain ⟨c, hc, hmap⟩ := @GlobalTheory.EvalNormTransfer.exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (GlobalTheory.EvalNormTransfer.borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hν0.2 (GlobalTheory.EvalNormTransfer.iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hSch : ∀ S' ∈ MultR R F, ∃ c', IsMultIP (MP R) R.ν0 R.fd0 S' S' c' := fun S' hS' =>
    GlobalTheory.MultFinite.schurMult hCusp R.ν0 R.fd0 hinf hνH hν0.2 S' hS' S' hS'
  have hcont : ∀ S' ∈ MultR R F, ∀ v, Continuous (S' v) ∧ ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S' v (γ * g) = S' v g :=
    fun S' hS' v => Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := JR R F) (χ := chiR R F) hS' v
  haveI : BorelSpace (GA D (D.sp.Y 0)) := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : ∀ S' ∈ MultR R F, ∀ v, MemLp (S' v) 2 (R.ν0.restrict R.fd0) := by
    intro S' hS' v
    obtain ⟨c', hip⟩ := hSch S' hS'
    refine (memLp_two_iff_integrable_sq_norm (hcont S' hS' v).1.measurable.aestronglyMeasurable).2
      (((hip v v).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) (hcont S hS v₀).1 (hcont S hS v₀).2 (hL2 S hS v₀)
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq (hSch S hS) hv).symm), ?_⟩
  intro h0
  refine GlobalTheory.EvalAllRows.eq_zero_of_units (MP R) S fun v hv' => ?_
  by_contra hne
  have hre := re_ipM_eq (hSch S hS) hv'
  have hint : IntegrableOn (fun x => ‖S v x‖ ^ 2) R.fd0 R.ν0 :=
    (memLp_two_iff_integrable_sq_norm (hL2 S hS v).aestronglyMeasurable).1 (hL2 S hS v)
  have hp := Formalism.IndefR.PeterssonHilbertSpace.petPos (D.sp.Y 0) R.ν0 R.fd0 hνH hν0.2 (S v) (hcont S hS v).1 (hcont S hS v).2 hne hint
  rw [← hre, h0] at hp
  exact lt_irrefl _ hp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRowsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  first | exact @GlobalTheory.EvalAllRows.evalTranslate_norm_all | exact GlobalTheory.EvalAllRows.evalTranslate_norm_all | (intros; apply GlobalTheory.EvalAllRows.evalTranslate_norm_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientModelConjDiscreteSeriesOfGap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientModelConjDiscreteSeriesOfGap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjVecLow

open _root_.Formalism.L2.SG.InstExistsPf

theorem lowKSub_le_sm_of_unique {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp) (τ : D.what₂.Tau)
    (hone : ∀ S S' : Submodule ℂ (M.H τ),
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S →
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S' → S = S') :
    Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  obtain ⟨S, hS, hSle⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V Sp M τ
  exact le_trans (sSup_le fun S' hS' => (hone S' S hS' hS).le) hSle

theorem gap_rows {D : D7} (hG : GapHyp D) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.GapAtLeast (fun i : Fin n => Formalism.MainNotions.S.epsS D.R (Fin.cast hn i))
      (fun i : Fin n => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast hn i)) (16 * (D.R.r : ℝ) ^ 19) := by
  subst hn
  have h := Formalism.L2.SG.Pf.BunD.gap_lamS D.R (D.hc τ) (h := 16 * (D.R.r : ℚ) ^ 19) (by positivity)
    (fun j hj => hG.2 τ j hj)
  intro a b hab
  have := h a b (by simpa using hab)
  push_cast at this
  simpa using this

theorem npq_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) :
    (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1 < 16 * (n : ℝ) ^ 19 := by
  have hp : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hq : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp' : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h3 : (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hp' (by positivity)) hq' (by positivity) (by positivity)
    nlinarith
  have h19 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 19 := pow_le_pow_right₀ hn' (by norm_num)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 19 := one_le_pow₀ hn'
  linarith

theorem exists_conj_intertwiner_of_gap (hUq : GlobalTheory.Published.DiscreteSeriesUpqUnique) {D : D7} (hG : GapHyp D)
    (I : Formalism.MainNotions.S.AutInst) (hI : I = instOf D)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (n_eq : I.n = D.R.r)
    (eps_eq : ∀ v (i : Fin I.n), I.ε v i = Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i))
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (lam_eq : ∀ v (i : Fin I.n), lam v i = Formalism.MainNotions.S.lamS D.R (D.hc (pl v)) (Fin.cast n_eq i))
    (ds : ∀ v, Formalism.MainNotions.S.IsDS (I.ε v) (lam v) (σ v)) (low : ∀ v, Formalism.MainNotions.S.IsLowUnit (I.ε v) (lam v) (σ v) (w v))
    (N : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) :
    ∃ c : ∀ τ, N.H τ ≃ₗᵢ⋆[ℂ] H (pl.symm τ),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ m : Matrix (Fin I.n) (Fin I.n) ℂ,
        HEq m ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ) → ∀ x, c τ (N.rep τ g x) = σ (pl.symm τ) m (c τ x)) ∧
      ∀ τ, (c τ).symm (w (pl.symm τ)) ∈ N.sm τ := by
  subst hI
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 hUq
  let M0 : DSModel (D.sp.Y 0) (parA (tparRec D) 0) :=
    { H := fun τ => H (pl.symm τ)
      σ := fun τ => σ (pl.symm τ)
      lam := fun τ => lam (pl.symm τ)
      ε := fun τ => (instOf D).ε (pl.symm τ)
      fr := fun τ => (GlobalTheory.SeeInt.frP D τ)⁻¹
      enum := fun τ => by
        have e1 : lam (pl.symm τ) = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by rw [lam_eq, Equiv.apply_symm_apply]
        have e2 : (instOf D).ε (pl.symm τ) = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) :=
          funext fun i => eps_eq _ i
        rw [e1, e2]
        exact GlobalTheory.RowLev.isEnum_parA_zero D n_eq τ
      ds := fun τ => ds _
      fr_unit := fun τ => Matrix.isUnit_nonsing_inv_iff.mpr ((instOf D).P_unit _)
      fr_gram := fun τ => GlobalTheory.SeeInt.fr_gram D τ }
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M0
  obtain ⟨U, hUi⟩ := hU.exists_intertwiner (M := (M' : DSModel (D.sp.Y 0) (parB (tparRec D) 0))) (M' := N)
  have key : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ x,
      c τ (U τ (N.rep τ g x)) = M0.rep τ g (c τ (U τ x)) := by
    intro τ g hg x
    exact (congrArg (c τ) (hUi τ g hg x)).trans (hc τ g hg _)
  refine ⟨fun τ => (U τ).trans (c τ), ?_, ?_⟩
  · intro τ g hg m hm x
    have hm' : m = (GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ := eq_of_heq hm
    show c τ (U τ (N.rep τ g x)) = σ (pl.symm τ) m (c τ (U τ x))
    rw [key τ g hg x, hm']
    show σ (pl.symm τ) ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * ((GlobalTheory.SeeInt.frP D τ)⁻¹)⁻¹) _ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.SeeInt.frP_unit D τ)]
  · intro τ
    have hone : ∀ S S' : Submodule ℂ (M0.H τ),
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S →
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S' → S = S' := by
      have hHC := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M0.enum τ).1 (M0.ds τ)
      haveI : CompleteSpace (M0.H τ) := (M0.ds τ).1
      have hgap : Formalism.QuantumDeterminants.GapAtLeast (M0.ε τ) (M0.lam τ) (16 * (D.R.r : ℝ) ^ 19) := by
        have e1 : M0.ε τ = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) := funext fun i => eps_eq (pl.symm τ) i
        have e2 : M0.lam τ = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by
            show lam (pl.symm τ) i = _
            exact (lam_eq (pl.symm τ) i).trans (by rw [Equiv.apply_symm_apply])
        rw [e1, e2]
        exact gap_rows hG n_eq τ
      have hr : (D.sp.Y 0).rank = D.R.r := n_eq
      have hbig : ((D.sp.Y 0).rank : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (M0.ε τ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf (M0.ε τ) : ℝ) + 1 <
          16 * (D.R.r : ℝ) ^ 19 := by
        have h1 : 1 ≤ (D.sp.Y 0).rank := by have := hG.1; omega
        exact (npq_lt (M0.ε τ) h1).trans_eq (by rw [hr])
      exact (ReciprocityTheory.ChartRestriction.DS.isDS_props_of_gap _ _ _ hHC _ hgap hbig _ _ (M0.ds τ)).2.1
    have hw : w (pl.symm τ) ∈ M0.sm τ := lowKSub_le_sm_of_unique M0 τ hone (low _).2
    set e := (U τ).trans (c τ) with he
    have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
        e.symm (M0.rep τ g y) = N.rep τ g (e.symm y) := by
      intro g hg y
      apply e.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      have := key τ g hg (e.symm y)
      change e (N.rep τ g (e.symm y)) = M0.rep τ g (e (e.symm y)) at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    exact GlobalTheory.ConjMult.span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit _ τ) e.symm hint hw

theorem conjModel_of_gap : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  intro _ _ hUq _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE hG _ hinf _ _
  have key : (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y :=
    GlobalTheory.IotaReal.iota_real_finite_of_eq R.θ hinf X.B.I h X.ιE X.pl X.φ_eq hιE
  obtain ⟨-, hreal, -⟩ := key
  obtain ⟨c, hc1, hc2⟩ := exists_conj_intertwiner_of_gap hUq hG X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ X.B.w
    X.B.lam X.lam_eq X.ds X.low (MP R)
  exact ⟨c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x, hc2⟩

end GlobalTheory.ConjVecLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientModelConjDiscreteSeriesOfGapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientModel_conjDiscreteSeries_of_gap : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  first | exact @GlobalTheory.ConjVecLow.conjModel_of_gap | exact GlobalTheory.ConjVecLow.conjModel_of_gap | (intros; apply GlobalTheory.ConjVecLow.conjModel_of_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 1000000 in
theorem evalOn_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  intro hDS hCusp hU hFin D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE hGap hl hi hν hsee
  obtain ⟨cc, hcc, hsm⟩ := GlobalTheory.T.contragredientModel_conjDiscreteSeries_of_gap hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  let v₀ : (MP R).Vec := fun τ => ⟨(cc τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, cc τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(cc τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  have hI := GlobalTheory.T.conj_translated_level_row_evaluation_mem_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  have hO := GlobalTheory.T.exists_rowLevel_translatedEvaluation_of_conj_row hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  refine ⟨v₀, hnorm, c0, hc0, ?_⟩
  classical
  have hmem : ∀ S : MultR R F, MemLp (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) 2 (muX X) :=
    fun S => (hN v₀ hnorm S S.2).1
  let Φ : MultR R F → conjRows X := fun S =>
    ⟨(hmem S).toLp _, hI S S.2 _ (hmem S).coeFn_toLp⟩
  have hΦ : ∀ S, ((Φ S : conjRows X) : L2X X) =ᵐ[muX X]
      (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) := fun S => (hmem S).coeFn_toLp
  have key : ∀ (S : MultR R F) (Fx : conjRows X), ((Fx : L2X X) =ᵐ[muX X]
      fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) → Φ S = Fx := by
    intro S Fx hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ S).trans hF.symm
  let L : MultR R F →ₗ[ℂ] conjRows X :=
    { toFun := Φ
      map_add' := fun S S' => by
        apply key
        have h1 := hΦ S
        have h2 := hΦ S'
        have h3 := Lp.coeFn_add ((Φ S : conjRows X) : L2X X) ((Φ S' : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a S => by
        rw [RingHom.id_apply]
        apply key
        have h1 := hΦ S
        have h3 := Lp.coeFn_smul a ((Φ S : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hLn : ∀ S : MultR R F, ‖((L S : conjRows X) : L2X X)‖ ^ 2 =
      c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re := by
    intro S
    show ‖((hmem S).toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp (hmem S)]
    exact (hN v₀ hnorm S S.2).2.1
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S hS
    have h1 := hLn S
    rw [hS] at h1
    simp only [ZeroMemClass.coe_zero, norm_zero, zero_pow two_ne_zero] at h1
    have h2 := (mul_eq_zero_iff_left hc0.ne').mp h1.symm
    exact Subtype.ext ((hN v₀ hnorm S S.2).2.2 h2)
  have hsurj : Function.Surjective L := by
    intro Fx
    obtain ⟨S, hS, hF⟩ := hO (Fx : L2X X) Fx.2
    exact ⟨⟨S, hS⟩, key ⟨S, hS⟩ Fx hF⟩
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun S => ⟨hΦ S, hLn S⟩⟩

end GlobalTheory.Mem.SRe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestVector_evaluation_identifies_levelRows_conj : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  exact GlobalTheory.Mem.SRe.evalOn_all
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensio
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem levCols_le_triv_and_finite : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  intro hF _ D G' _ _ Pl0 T A Ks _ _ _ R F _ hi _
  refine ⟨GlobalTheory.Mem.Th.EEat_le_triv R _, ?_⟩
  obtain ⟨U, hU, hJ⟩ := GlobalTheory.DefiniteEnd.exists_open_level (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
  exact GlobalTheory.MultFinite.hcFinite hF hi ⟨U, hU, fun k hk hk' => by
    obtain ⟨h1, h2⟩ := hJ k hk
    have hm : k ∈ levS (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) := ⟨hk', h1⟩
    have hc : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) k = 1 := congrArg Units.val h2
    obtain ⟨h3, h4⟩ := GlobalTheory.Mem.Th.principal_le_level (R.βY 0) (R.dat0 (R.levR F true)) (R.dat0 (R.levR F true)).P k hm
    exact ⟨h3, h4.trans hc⟩⟩

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensioStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  first | exact @GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | exact GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | (intros; apply GlobalTheory.Mem.SRe.levCols_le_triv_and_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrank
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation _root_.Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_conjRows_eq {D : D7} (X : HidaSetting D) :
    Module.finrank ℂ (conjRows X) = Module.finrank ℂ (HHX X) := by
  let e := conjL (muX X)
  let j : conjRows X ≃+ HHX X :=
    { toFun := fun f => ⟨e f, f.2⟩
      invFun := fun g => ⟨e.symm g, by
        show e.toLinearEquiv.toLinearMap (e.symm g) ∈ HHX X
        simpa using g.2⟩
      left_inv := fun f => by ext1; simp
      right_inv := fun g => by ext1; simp
      map_add' := fun f g => by ext1; simp }
  have hbij : Function.Bijective (starRingEnd ℂ : ℂ → ℂ) :=
    Function.Involutive.bijective (fun z => by simp)
  have hr := rank_eq_of_equiv_equiv (starRingEnd ℂ : ℂ → ℂ) j hbij (fun r m => by
    ext1
    show e (r • (m : L2X X)) = (starRingEnd ℂ r) • e m
    exact e.map_smulₛₗ r m)
  unfold Module.finrank
  rw [hr]

theorem exists_rowJ_and_finrank_HHX : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c eE hc hv₀ hE hrange hnorm hle hJ1 hJ2
  refine ⟨fun hD => ?_, exists_rowJ_of_evalOn hc hv₀ hE hrange hnorm hle hJ2⟩
  obtain ⟨J1, -⟩ := hJ1
  have hD' : D.what₂.Dall = Module.finrank ℂ (MultR R F) := hD
  rw [hD', J1.finrank_eq, finrank_conjRows_eq]

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  first | exact @GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX | exact GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX | (intros; apply GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStages
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem exists_sRest_top : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro hDS hHC hCusp hDSU hRF D G' _ _ Pl0 T A Ks _ _ _ R F F0 P eE hGap hph hL hR hDs hLev hGrp hPin hE0 hM hRange hNorm hDall
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_finiteAdelicPoint_carries_rowLevel D G' Pl0 T A Ks R F P.X P.inst P.pin hLev hGrp hPin hE0
  obtain ⟨v₀, hv, c, hc, hev⟩ :=
    GlobalTheory.T.lowestVector_evaluation_identifies_levelRows_conj hDS hCusp hDSU hRF D G' Pl0 T A Ks R F P.X P.inst t P.pin hGap hLev hM.inf hM.ν0 ht
  have hg := GlobalTheory.T.evaluation_goodRows_to_conjugate_goodRows D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c hLev hM.inf hv ht hev
  have hle := (GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional hHC hCusp D G' Pl0 T A Ks R F hLev hM.inf hM.ν0).1
  obtain ⟨hfr, j, hj⟩ :=
    GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c eE hc hv hM.HE hRange hNorm hle hev hg.1
  refine ⟨hfr hDall, j, t, c, hc, ht, hg.2, hj, ?_⟩
  intro N hh F' hs
  have hF := GlobalTheory.T.finX_spectralRedivisionFullChoices D ⟨P.toNew (hfr hDall) j, N, hh⟩ P.X P.Y P.fin
  obtain ⟨S, hS⟩ := exists_sRest_re D F0 P (hfr hDall) j N hh F' hs hF hph hL hR hDs
  exact ⟨hF, S, hS⟩

end GlobalTheory.Mem.SRe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStagesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectralLevel_objects_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  first | exact @GlobalTheory.Mem.SRe.exists_sRest_top | exact GlobalTheory.Mem.SRe.exists_sRest_top | (intros; apply GlobalTheory.Mem.SRe.exists_sRest_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStages
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.SRe

section Parts

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
  {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
  {F0 : ∀ u, Forms0 a.D u} (P : SPack a.D F0) {F₁ : ∀ u, Forms0 (reL a Z).D u} (hs : SameL a Z F0 F₁)
  (hF : FinX (reY Z P.Y))


set_option maxHeartbeats 4000000 in
def packL : SPack (reL a Z).D F₁ := (by with_unfolding_all exact ((P.re Z hs hF) :))


set_option maxHeartbeats 4000000 in
def restL (S : SRest (P.re Z hs hF)) : SRest (packL a Z P hs hF) := (by with_unfolding_all exact (S :))


set_option maxHeartbeats 4000000 in
theorem restL_j (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) :
    (restL a Z P hs hF S).j = (by with_unfolding_all exact (j.trans (eEECre Z P.G) :)) := (by with_unfolding_all exact (hS :))


set_option maxHeartbeats 4000000 in
theorem nonempty_sAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H)
    (t : GA a.D (a.D.sp.Y 0)) (c : ℝ) (hc : 0 < c) (see : SeeAt R F P.X P.inst t)
    (ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c)
    (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (rowJ : RowJ R eE P.X P.inst P.G t j)
    (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) : Nonempty (SAtL a Z R F eE F₁) := by
  have h1 := mvRowJ a Z R P.X P.inst P.G t eE j rowJ
  have h2 := restL_j a Z P hs hF j S hS
  letI := alg (reL a Z) iK
  exact ⟨{ P := packL a Z P hs hF
           S := restL a Z P hs hF S
           t := tL a Z t
           c := c
           c_pos := hc
           see := (by with_unfolding_all exact ((mvSee a Z R F P.X P.inst t see) :))
           ev := (by with_unfolding_all exact ((mvEv_holds a Z R F P.X P.inst P.G t c ev) :))
           rowJ := by rw [h2]; exact (by with_unfolding_all exact (h1 :)) }⟩

end Parts


set_option maxHeartbeats 4000000 in
theorem satOfDiscreteSeries : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  intro h1 h2 h3 h4 h5 B C a G' _ _ Pl0 T A Ks _ _ _ R F F0 eE P hG hI hL hRT hDs hLev hgl hPin hE0 hMod hRg hN hDall
  obtain ⟨hD, j, t, c, hc, see, ev, rowJ, rest⟩ := GlobalTheory.T.exists_spectralLevel_objects_replacedStages h1 h2 h3 h4 h5 a.D G' Pl0 T A Ks R F F0 P eE hG hI hL hRT hDs
    hLev hgl hPin hE0 hMod hRg hN hDall
  refine ⟨P.toNew hD j, fun N hh F₁ hs => ?_⟩
  obtain ⟨hF, S, hS⟩ := rest N hh _ hs
  exact nonempty_sAtL a _ P hs hF R F eE t c hc see ev j rowJ S hS

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStagesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectralObjects_over_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  first | exact @GlobalTheory.Mem.SRe.satOfDiscreteSeries | exact GlobalTheory.Mem.SRe.satOfDiscreteSeries | (intros; apply GlobalTheory.Mem.SRe.satOfDiscreteSeries <;> assumption)
end
