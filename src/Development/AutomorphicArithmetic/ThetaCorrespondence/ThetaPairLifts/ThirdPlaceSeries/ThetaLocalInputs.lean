module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelectedRealization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamPOfPart
public import Lean
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRows
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendsFineAdelicDatumLargerFieldOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEigMemFixedField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteSplittingSetFrobeniusPolynomials
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegrality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecond

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.NRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
structure ThetaLocalInputsAlt : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geo : GlobalTheory.Published.GeometricLemma
  unl : GlobalTheory.Published.UnlinkedProductIrreducible
  mp : GlobalTheory.Published.DepthZeroJacquetInjective
  js : GlobalTheory.Published.JacquetShalika
  fin : GlobalTheory.Published.AutomorphicFormsFiniteGL
  gal : _root_.UpperTheory.GalS.CuspUAlt
  car : _root_.UpperTheory.GalS.CarUAlt
  clo : GlobalTheory.Published.RegularAlgebraicPurity
  art : GlobalTheory.Published.GlobalArtinReciprocity
  chA : GlobalTheory.Published.HeckeLAdicCharacterAbove
  chP : _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt
  berger : GlobalTheory.Published.DeRhamPotSemistable
  cheb : GlobalTheory.Published.ChebotarevDegreeOne
namespace Inputs
end Inputs
end GlobalTheory.NRows
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (E →+* Qbar l) → Multiset ℤ} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
theorem IsGalUAlt.aw_locPar (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w) :
    Aw (wdOf h hl ι r) ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2)) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h]
  exact H.aw hl (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hσ
theorem IsGalUAlt.eq_locPar (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w)
    (hu : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).unr) :
    wdOf h hl ι r = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) :=
  (H.aw_locPar hL hF hl h).eq_unr ((WD.unr_tw _ _).2 hu)
omit [IsCMField E] in
theorem unr_rec_of_has_sat {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr := by
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake hrc (σ := ParLaws.toRep σ) hα
  have e' : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  rw [e', WD.unr_mk]
  exact WDRep.unr_diag _
theorem exists_aw_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : CG E a)
    (hc : π.IsCsd) (hr : π.IsRegAlg) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        Aw (wdOf h hl ι r) ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpTw ((1 - (a : ℝ)) / 2)) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι ha (π := π) hr hc
  exact ⟨r, Units.continuous_val.comp H.cont, H.ss, fun w hl A h => H.aw_locPar hL hF hl h⟩
theorem nice_of_loc_par (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (h : IsPlaceOver A w)
    (k : NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2))) : _root_.UpperTheory.GalS.NiceAlt π h := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  refine ⟨σ, hσ, _, _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h, ?_⟩
  rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) σ]
  rwa [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h] at k
theorem nice_of_spherical' {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (hs : SmGL.IsSpherical σ.ρ) : _root_.UpperTheory.GalS.NiceAlt π h := by
  refine ⟨σ, hσ, rc, hrc, NcW.of_unr ?_⟩
  rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt hrc, WD.unr_tw]
  exact (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hrc (ParLaws.toRep σ)).2 hs
end UpperTheory.GalS
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem exists_hasSatake_of_unr_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))}
    (hu : (rc (cls σ)).unr) : ∃ α, HasSatake σ.ρ α := by
  obtain ⟨m, c, e⟩ := Unram.exists_diag hu
  have H' := H
  first | (have hOpn := UpperTheory.One.M.opn _ (H'); obtain ⟨_, _, _, H'⟩ := hOpn) | obtain ⟨_, _, _, -, H'⟩ := H'
  obtain rfl : a = m := by simpa [e] using (H'.dim (cls σ)).symm
  obtain ⟨τ, hτ⟩ := exists_hasSatake (k := w.adicCompletion E) fun i => (c i)⁻¹
  have e2 := _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hτ
  simp only [inv_inv] at e2
  have g : UpperTheory.Zero.LLC.Good (cls σ) :=
    (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _ _ ((H'.sph _).2 hu)).2
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := τ.ρ) (σ := σ.ρ) (hs := τ.smooth) (hi := τ.irr) (hs' := σ.smooth) (hi' := σ.irr)).1
    (_root_.UpperTheory.One.M.LawsM.inj H' (cls τ) (cls σ) g (e2.trans e.symm))
  exact ⟨_, σ.irr, fixed_ne_bot_of_equiv φ hτ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hτ.2.2⟩
end UpperTheory.One.M
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepresentationTheoryHypotheses
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.Mem.LiteralAutomorphy
open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published
structure LocalRepresentationTheoryHypothesesAlt : Prop where
  bz : BernsteinZelevinskyFiniteness
  bern : BernsteinUnitaryProductIrreducible
  geo : GeometricLemma
  zel : ZelevinskyPolynomialRing
  disj : TotallyDisjointProductIrreducible
  mp : MoyPrasadJacquetIso
  temp : TemperedProductOfSquareIntegrable
  seg : EssSquareIntegrableSegments
  sq : SquareIntegrableSegment
  gen : GenericUnlinkedGL
  multi : LanglandsMultisegments
  exh : LanglandsExhaustionGL
  cos : StandardCosocleGL
  llc : _root_.UpperTheory.Zero.LLC.RecTExists
  conv : LocalConverseGL
  dzi : DepthZeroInduction
  brauer : BrauerDegreeZero
  chev : ChevalleyUnits
  green : GreenRegularCharacters
structure GlobalAutomorphicGaloisHypotheses' : Prop where
  decay : CuspRapidDecay
  hc : HarishChandraFinite
  fin : AutomorphicFormsFiniteGL
  js : JacquetShalika
  cusp : CuspidalSpectrumGL
  bc : _root_.GlobalTheory.Published.BaseChangeIsobaricTransfer
  gk : GelfandKazhdanDual
  gal : _root_.UpperTheory.GalS.PairUAlt
  car : _root_.UpperTheory.One.M.Row
  pur : ClozelPurity
  coh : ClozelCohomological
  art : GlobalArtinReciprocity
  ray : RayClassFieldSt
  chA : HeckeLAdicCharacterAbove
  chW : AlgebraicCharacterWD
  berger : DeRhamPotSemistable
end GlobalTheory.Mem.LiteralAutomorphy
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieAutAndSplit
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.AutomorphismSplitting
theorem tieAut_and_split_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut ∧ ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v) := by
  intro hAF hL D P
  have hcsd : IsCSD D.host P.cf.eta := GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ P.cf.isEta
  have hE : (P.chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [P.chr.etaT]; exact P.cf.isEta.inf⟩
  have hE' : (P.chr.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => (-(1 / 2) : ℚ)) :=
    ⟨fun _ => -1, fun _ => by norm_num, by rw [P.chr.etaTinv]; exact hasInf_inv P.cf.isEta.inf⟩
  refine ⟨⟨⟨?_, ?_⟩, fun τ => ?_, fun w => ?_, fun i w => ?_⟩, fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩
  · rw [P.chr.csd, P.chr.etaT]; exact hcsd
  · rw [P.chr.csd, P.chr.etaTinv]; exact isCSD_inv' hcsd
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
    · have ht : τ = embPsi D.host (D.eTau ρ) := h.symm
      rw [ht, (P.chr.infG _ _ hE (D.eTau ρ)).1, (P.chr.infG _ _ hE' (D.eTau ρ)).1]
      refine ⟨Or.inl (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; rfl
    · have ht : τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) := by
        rw [← h]; ext x; rfl
      rw [ht, (P.chr.infG _ _ hE (D.eTau ρ)).2, (P.chr.infG _ _ hE' (D.eTau ρ)).2]
      refine ⟨Or.inr (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; ring_nf
  · have hu : D.naut.unr (D.naut.locG D.naut.etaT w) := D.naut.etaT_unr w
    rw [D.naut.tempered_unr _ hu, P.chr.frob _ w ((P.chr.unr_iff _ w).1 hu)]
    intro α hα
    rw [Multiset.mem_singleton] at hα
    subst hα
    have h1 : ‖(((P.chr.e1 D.naut.etaT).1.val w : ℂˣ) : ℂ)‖ = 1 :=
      (P.chr.e1 D.naut.etaT).2 _
    rw [Units.val_inv_eq_inv_val, norm_inv, h1, inv_one]
  · obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E (P.chr.e1 (D.naut.muC i)).1 w
    have he := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P (D.naut.muC i) w ξ hξ
    rw [P.T.tempered, he]
    refine GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig _ _ _ _ _ _ ?_ ?_
    · rw [← he, P.T.dim, D.naut.locG_dim]
    · intro φ _ α hα
      exact _root_.UpperTheory.Zero.LLC.IsRecT.recUnit (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) ξ
        (Irr.ofDet 1 ξ hξ.1) (hξu (P.chr.e1 _).2) ⟨Representation.Equiv.refl _⟩ φ α hα
end GlobalTheory.AutomorphismSplitting
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SPairs
set_option synthInstance.maxHeartbeats 200000

section
open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair
namespace UpperTheory.GalS
theorem cusp_of_pair_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (hP : _root_.UpperTheory.GalS.PairUAlt) : _root_.UpperTheory.GalS.CuspUAlt := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
  exact hP E Ω l ι a ha π χ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩
theorem carU_of_finite_gl_recT : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.UpperTheory.GalS.CarUAlt → _root_.UpperTheory.GalS.CarUAlt := fun _ _ h => h
theorem carU_of_regular_algebraic_purity (H : _root_.UpperTheory.GalS.CarUAlt) (_ : GlobalTheory.Published.RegularAlgebraicPurity) : _root_.UpperTheory.GalS.CarUAlt := H
end UpperTheory.GalS
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LlOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (k := w.adicCompletion E) → WD h}
namespace Old
end Old
namespace New
theorem llOf_alt : RecTExists → LocalConverseGL → DepthZeroInduction →
    BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → RecTExists :=
  fun h _ _ _ _ _ _ _ _ _ _ _ => h
end New
end UpperTheory.One.M
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultQ
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta GlobalTheory.Mem.Th
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.DIV _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
structure EllipticHypothesis : Prop where
  e1 : GlobalTheory.TwSys.Cheb
  e2 : GlobalTheory.Published.PoitouTateTotallyComplex
  e3 : GlobalTheory.Published.CohDimTwo
  e4 : GlobalTheory.Published.TameLocal
  e5 : LocalFiniteness
  e6 : LocalTateDuality
  e7 : LocalEulerChar
  e8 : GlobalFiniteness
  e9 : GlobalEulerChar
  e10 : UnramifiedOrthogonality
  e11 : BlochKatoReduction.Gen.ArchimedeanSignatureMatching
  e12 : GreenbergWiles
  e13 : GlobalTheory.Published.RayCharacterArtin
  e14 : GlobalTheory.Published.ChebotarevDegreeOne
  e15 : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator
  e16 : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  e17 : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  e18 : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  e19 : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  e20 : GlobalTheory.HeckeSupSt.HeckeReadTie
  e21 : GlobalTheory.Published.AutomorphicFormsFiniteGL
  e22 : _root_.UpperTheory.GalS.CuspUAlt
  e23 : GlobalTheory.Published.DeRhamPotSemistable
  e24 : _root_.UpperTheory.GalS.CarUAlt
  e25 : ∀ D : D7, LocalSituation.Conclusion5 D
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
def MultiplicityCondition {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Prop :=
  GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat
end
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Has3NeoOfSteps
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Top.Bl
theorem has3_neo_of_localLanglands_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (hB : ExistsUnlocalizedSaturatedState) (hA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL) (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL)
    (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) (hB0 : _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep) (hB1 : _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) (hB2 : _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep) (hC : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL) (hFin : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep)
    (S : SExt) (Γ : GeoP) : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) := by
  have h := StepW.and hB (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
  refine h.trans (StepW.of_all ?_)
  intro K B f T w _ _ H
  obtain ⟨⟨P, x, sat, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
  obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
  obtain ⟨imt⟩ := mt P x1
  obtain ⟨irat⟩ := rat P x1 la
  have li : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
  obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
  obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
  obtain ⟨sc⟩ := c P x4 l2
  obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ ⟨p4 (p3 p2), sat⟩
  exact ⟨Z, ⟨v⟩⟩
end GlobalTheory.Mem.Top.Bl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringRankOfDescentSteps
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
theorem covering_rank_of_descent_steps_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative →
    _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverRank := by
  intro hX h1 h2 h3 hS hT hL h4 h5 h6 h7 h8
  refine Formalism.MainNotions.Closed.imp (_root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt hX h1 hS hT h2 h3 hL h4 h5 h6 h7 h8) ?_
  rintro _ Fm _ _ ⟨C, h0, a, h⟩
  refine ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => ?_⟩
  have H := h x hx hle ι p hp i hi Y hY 1 le_rfl (by norm_num)
  rw [Nat.cast_one, one_mul] at H
  refine H.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact add_le_add le_rfl (min_le_right _ _)
end GlobalTheory.CovTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverRank_of_coverDegree_and_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverRank := by
  first | exact @_root_.GlobalTheory.CovTop.covering_rank_of_descent_steps_alt | exact _root_.GlobalTheory.CovTop.covering_rank_of_descent_steps_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_rank_of_descent_steps_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTup
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTup
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroMem
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem conj_mem_K_two_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hone : ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W),
      (∀ PP ∈ (_root_.GlobalTheory.BaseChain.com_z W).Pg, redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP (finE (D.sp.Y 0) k) = 1) →
      (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) :
    ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W), (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2 := by
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (D.sp.Y 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (D.sp.Y 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (D.sp.Y 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G h0 hBot
    (fun k : GA D (D.sp.Y 0) => (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) ?_ ?_ ?_ hone
  · intro (k : GA D (D.sp.Y 0)) _ (k' : GA D (D.sp.Y 0)) _ q q'
    show (iotaX W.S.X W.Q.instEq (s * (k * k') * s⁻¹)).2 ∈ W.S.X.K2
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [e, map_mul, Prod.snd_mul]
    exact W.S.Y.hK.2.1 _ q _ q'
  · intro PP (n : GA D (D.sp.Y 0)) q hn _ _ hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hk' : t⁻¹ * n * t ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) := by rw [ht]; exact hk
    have hKs := ((hSt (s * (t⁻¹ * n * t) * s⁻¹)).1 ⟨GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s _ hk'.1, by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.conj_mem_St_iff]; exact parLev_St hk'.2.1⟩).2
    have hN := ((B.tieN _).1 (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn')).2
    have goal : (iotaX W.S.X W.Q.instEq (s * (t⁻¹ * n * t) * s⁻¹)).2 ∈ W.S.X.K2 := by
      rw [e] at hKs ⊢
      generalize embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹ = n' at hN hKs ⊢
      rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply] at hKs ⊢
      generalize iotaX W.S.X W.Q.instEq n' = y at hN hKs ⊢
      change (W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u ∈ _ at hKs ⊢
      refine Formalism.L2.SG.Pf.unipotent_conj_mem_level hN ?_
      have := Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (W.S.X.xu_K u) hKs)
        (Formalism.L2.SG.Pf.unitaryCongruence.K_inv _ (W.S.X.xu_K u))
      rwa [show W.S.X.xu u * ((W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u) * (W.S.X.xu u)⁻¹ = y.2 by group] at this
    subst ht
    exact goal
  · intro b hb hk
    rw [← hemb b] at hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hPk u f B hTr hAd a₀ hH0 b hb).1.1 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [← e] at h1
    rw [← hemb b]
    subst ht
    exact h1.2
set_option maxHeartbeats 2000000 in
theorem mem_K_two_iff_of_family_character (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0))
    (hκS : finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) :
    (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔
      rTup (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈
        (_root_.GlobalTheory.LevZero.datZero_alt W).P.H := by
  obtain ⟨hr, ξ, hL⟩ := hBot.mem.lev
  obtain ⟨N, hN, -⟩ := hBot.mem.base
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := hBot.mem.rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hr' : D.R.r ≤ (D.sp.Y 0).rank := hr
  have hLb : _root_.GlobalTheory.LevZero.datZero_alt W = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
      (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := hL
  have hlift : Lev.LiftsExist (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) :=
    GlobalTheory.ChainOnto.FlagAct.liftsExist_stage hBot.com hBot.mem
  obtain ⟨m, hm⟩ := GlobalTheory.MemMatch.exists_read W.S.X W.Q.instEq (_root_.GlobalTheory.BaseChain.com_z W).Pg hBot.typ hBot.com.split
    (fun PP => ⟨_, (hBot.loc PP).idem⟩) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) N hN s hSt
  have hin := _root_.GlobalTheory.LevZeroMem.conj_mem_K_two_alt W hPk f B G hBot h0 hBl hAd hTr a₀ hH0 a hac t s ht hs hSt (fun k hk h1 =>
    (hm k hk.1 (parLev_St hk.2.1)).2 fun PP => by rw [h1 PP.1 PP.2, mul_one, mul_inv_cancel]; exact one_mem _)
  have hpat : ∀ g : ∀ PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP PP.1),
      g ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H ↔ ∀ PP, GlobalTheory.SymRes.IsPat D.R.rS D.R.k (g PP) :=
    fun g => (hBot.grp g).trans (forall_congr' fun PP => GlobalTheory.LevZero.exists_red_iff_isPat (G PP) PP.1 (hBot.loc PP).idem (g PP))
  rw [hLb] at hlift hin ⊢
  have hlev : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St (F := D.host.F) (E := D.host.E) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) →
      (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H →
      k ∈ levS (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
        (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := by
    intro k hk hS hP
    refine ⟨hk, ?_⟩
    show finE (D.sp.Y 0) k ∈ lev _ _ _ _
    rw [mem_lev, mem_parLev]
    exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
      fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP⟩
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hk₀ : k₀ ∈ GfC (D.sp.Y 0) := by
    have := GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s⁻¹ _ hκ
    rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
  have hfe : finE (D.sp.Y 0) (s * k₀ * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k₀ * (finE (D.sp.Y 0) s)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
  rw [hfe, GlobalTheory.FrameConj.rTup_conj]
  refine ⟨fun hK => ?_, fun hP => hin k₀ (hlev k₀ hk₀ hκS hP)⟩
  refine (hpat _).2 fun PP => (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 ?_
  haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot PP.1.asIdeal PP.1.ne_bot
  have hrr : (D.sp.Y 0).rank = D.R.k + (2 * D.R.rS + 1) := by
    have := le_antisymm hn hr'
    have h0' := h0
    unfold Ranks.r at this
    omega
  refine GlobalTheory.SymResCount.conj_pat_onto (kP PP.1) _ D.R.rS D.R.k hrr (m PP) (fun g hg => ?_) _ ((hm k₀ hk₀ hκS).1 hK PP)
  let g0 : ∀ Q : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP Q.1) := Function.update (fun _ => 1) PP (upperLeftBlock hr' g)
  have hg0 : g0 ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H := (hpat _).2 fun Q => by
    by_cases hQ : Q = PP
    · subst hQ
      simp only [g0, Function.update_self]
      exact (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 hg
    · simp only [g0, Function.update_of_ne hQ]
      exact GlobalTheory.SymRes.isPat_one _ _
  obtain ⟨k, hk, hkp, hkr⟩ := hlift g0
  have hkr' : (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) = g0 := hkr
  have h1 := (hm k hk (parLev_St hkp)).1 (hin k (hlev k hk (parLev_St hkp) (hkr' ▸ hg0))) PP
  have h2 : redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k) = g :=
    GlobalTheory.MemMatch.reductionBlock_injective_of_eq hr' hn _ _ ((congrFun hkr' PP).trans (Function.update_self _ _ _))
  rwa [h2] at h1
set_option maxHeartbeats 2000000 in
theorem mem_rowJ_iff_rTup_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  intro D L hT Gi Gl Kc Yd cX ex W hPk u f B hPl a₀ hH0 a _ hac hStab κ hκ hκS
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hvt, hsh, hpin, hread, hbt⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hPk u f B k ι v o n G pl ⟨hc, hv, hvt, hsh, hpin, hread, hbt⟩
  have h0 := h0_eq D
  have hκ1 : (iotaX W.S.X W.Q.instEq κ).1 = 1 := (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq κ).2 hκ
  show (iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔ _
  exact (and_iff_right hκ1).trans (_root_.GlobalTheory.LevZeroMem.mem_K_two_iff_of_family_character W hPk f B _ hBot h0 (hbt.lev h0) hbt.adapted hbt.trace a₀ hH0 a hac _ _ rfl rfl
    hStab κ hκ hκS)
end GlobalTheory.LevZeroMem
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTupStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  first | exact @_root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | exact _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | (intros; apply _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt <;> assumption)
end
end
end
