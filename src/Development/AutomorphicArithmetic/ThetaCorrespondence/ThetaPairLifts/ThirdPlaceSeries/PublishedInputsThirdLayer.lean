module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabels
public import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroInertiaOfLanglands
public import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity
public import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
public import Development.DiscreteGroups.GlobalIrreducibility.ActKEEqSelfLe
public import Development.DiscreteGroups.GlobalIrreducibility.RegularLocalOfDepthZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
structure PublishedInputsThirdLayerAlt : Prop where
  what₂ : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt
  decay : GlobalTheory.Published.CuspRapidDecay
  hc : GlobalTheory.Published.HarishChandraFinite
  greenC : GlobalTheory.Published.GreenCuspidal
  green : GlobalTheory.GLq.Green
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  ray : GlobalTheory.Published.RayClassFieldSt
  rayF : GlobalTheory.NT.RayField
  rayA : GlobalTheory.Published.RayCharacterArtin
  bc : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  std : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  howe : GlobalTheory.Hk3.HoweUnram
end GlobalTheory.HeightCounting.Up
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
variable {T : WDTie N A} (S : Reading T)
def LawsAlt : Prop :=
  ∀ (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), _root_.UpperTheory.One.M.RecLawsH (S i w hw).rc
end GlobalTheory.SplitRead
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRecLawsH
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC GlobalTheory.Published GlobalTheory.SplitRead
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
section Laws
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
theorem recLawsH_alt {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) :
    RecLawsH fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := H
  have hc : ∀ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1),
      Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
    rintro χ c ⟨φ⟩
    have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
      ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
    have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
      Units.continuous_map (continuous_matrix fun i j => by
        rw [Subsingleton.elim i j]; simpa using continuous_id')
    have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
      refine MonoidHom.ext fun z => congrArg χ ?_
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩
  have hmp : ∀ n (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π.ρ.Equiv π'.ρ) → cls π = cls π' :=
    fun n π π' e => congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 e)
  refine ⟨fun n π => H.dim _, fun n π π' hg => ⟨fun e => ?_, fun e => congrArg rc (hmp n _ _ e)⟩,
    fun n π π' e => congrArg rc (hmp n _ _ e), fun r t σ τ π hπ => _root_.UpperTheory.One.M.LawsM.prod H r t _ _ _ hπ, ?_, ?_, ?_, ?_⟩
  · have := _root_.UpperTheory.One.M.LawsM.inj H _ _ hg e
    exact IrrRep.cl_eq_iff.1 (eq_of_heq (Sigma.mk.inj this).2)
  · intro t χ c τ h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, congrArg rc (hmp t (toIrrRep τ) (IrrRep.det (Fin t) χ hχ) h2), H.det, sumList, List.foldr_map, speh]
    simp [List.foldr_map, ← List.map_eq_flatMap]
  · intro n χ c π π' hg h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, ← _root_.UpperTheory.One.M.LawsM.twist H (cls (toIrrRep π)) χ hχ hg]
    exact congrArg rc ((IrrGL.of_eq_of.2 h2).trans (IrrGL.tw_of π.π π.smooth π.irr χ hχ).symm)
  · intro n π
    rw [← H.sph]
    exact ⟨fixed_ne_bot_of_equiv (equivRep (toIrrRep π)).symm, fixed_ne_bot_of_equiv (equivRep (toIrrRep π))⟩
  · intro n π α hα
    have φ := equivRep (toIrrRep π)
    rw [H.sat (cls (toIrrRep π)) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩, WD.frobEig_diag]
end Laws
end UpperTheory.One.M
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.Mem.LiteralAutomorphy
structure NonEndoscopicHypothesesAlt : Prop where
  loc : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt
  aut : _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses'
  coh : LitCoh
  join : JoinOut
  fe : GlobalTheory.Published.HeckeTateFunctionalEquation
end GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Fc.S0
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure UnitaryGroupThirdPlaceHypotheses : Prop where
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  chebotarevDegreeOne : GlobalTheory.Published.ChebotarevDegreeOne
  galoisRepOfPolarizedCuspidal : _root_.UpperTheory.GalS.CuspUAlt
  baseChangeDefiniteUnitary : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup
  bhattScholzeCrystallineLattices : GlobalTheory.Published.BhattScholzeCrystallineLattices
  heckeLAdicCharacterAbove : GlobalTheory.Published.HeckeLAdicCharacterAbove
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  siegelWeilUnitaryConvergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  doublingMethod : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration
  unlinkedProductIrreducible : GlobalTheory.Published.UnlinkedProductIrreducible
  depthZeroJacquetInjective : GlobalTheory.Published.DepthZeroJacquetInjective
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL
  localGlobalAboveL : _root_.UpperTheory.GalS.CarUAlt
  regularAlgebraicPurity : GlobalTheory.Published.RegularAlgebraicPurity
  globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity
  heckeLAdicParameterAbove : _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt
  deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  rayCharacterArtin : GlobalTheory.Published.RayCharacterArtin
  genericUnitaryDualGL : GlobalTheory.Published.GenericUnitaryDualGL
  standardCosocleGL : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  siegelWeilUnitaryConvergent2 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  cMCurveGoodOutsidePrimeSt : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  weberRayFieldSt : GlobalTheory.Published.WeberRayFieldSt
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
  siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  litN : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt
  toHypothesesX : _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar
theorem UnitaryGroupThirdPlaceHypotheses.geometricLemma (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses) : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration P.bernsteinZelevinskyFiniteness P.geometricLemmaFiltration
end GlobalTheory.Fc.S0
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.Eig
section Satake
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.EigRows
open GlobalTheory.StdFrame (StdPsi tensCastR)
open GlobalTheory.Hk3 (hyp SphOp)
open GlobalTheory.HeckeScalarSph (locK)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {Q : principalLevelFrame.RowPsi V n}
end Satake
section Rows
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
  GlobalTheory.HeightCounting GlobalTheory.EigRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 400000
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Sb Sb' : Finset (PlE D.host)}
set_option maxHeartbeats 1000000 in
theorem eigTrue_of_read (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0)
    (W : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : RowSide D) {sat : D.what₂.FT → PlE D.host → Multiset ℂ}
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D (typeR Y) (fun σ w => W.e w (Rw.locR σ w)) sat)
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (he : EigAd Y Sb eig) (hsub : Sb ⊆ Sb') (hlow : Low D Sb') :
    EigTrue D R.C Rw Sb' eig := by
  intro j σ hne hgood P hs hP
  obtain ⟨s, rfl⟩ := GlobalTheory.TypeBlockPf.splitAt D P hs
  have hQ := stdPsi_PW Y j
  obtain ⟨_, B₀, -, hB₀⟩ := exists_hkDat (Sb := Sb) F hlev hsub hlow j hs hP (Nat.zero_le _)
  obtain ⟨x, hx, hx0⟩ := exists_sphVec hQ (partR_ne_bot Y hne) hB₀.full
  have hK : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.r s.v, NG.rt D.host.E D.R.r κ x = x := fun κ hκ =>
    hx.2 κ ((hyp_iff hQ s κ).2 hκ)
  obtain ⟨τ, hτ⟩ := exists_isLocS (typeR Y σ) s hx.1 hx0 hK
  have hrec := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)
  have hu := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hrec τ).2 (isSpherical_of_isLocS (typeR Y σ) s τ hτ hx.1 hx0 hK)
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt hrec hu
  have hpar : W.e s.w (Rw.locR σ s.w) = _ := hrow.1 σ s τ hτ
  have hunr : D.naut.unr (Rw.locR σ s.w) := (W.unr _ _).2 (hpar ▸ hu)
  refine ⟨hunr, fun k _ hk => ?_⟩
  obtain ⟨a, B, hd, -⟩ := exists_hkDat (Sb := Sb) F hlev hsub hlow j hs hP hk
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 : hkNorm R j k s.w • heckeOn _ B (readW Y j y) = _ • readW Y j y := he j σ k s.w a B hd hgood y hy
  rw [heckeOn_partR Y hlev j (hlow.offPg hlev hP) hk hd.elt hd.reps σ ((mem_isot_iff Y j σ y).1 hy), smul_smul] at h1
  have h2 := smul_left_injective ℂ (fun h => hy0 (readW_injective Y j (h.trans (map_zero _).symm))) h1
  have h3 := sphEig_eq_satEig hQ (typeR Y σ) s ((GlobalTheory.PlaceDict.isSplit_iff_conjPl_ne D _ s.w rfl).2
    (GlobalTheory.HeckeDatumExists.conj_ne_of_split hs)) τ hτ hα hk
  have hq : Formalism.UG.qV D.host.E s.w = normV s.w := Ideal.absNorm_apply _
  have h4 : D.naut.frobEig (Rw.locR σ s.w) = Finset.univ.val.map fun i => (((α i)⁻¹ : ℂˣ) : ℂ) := by
    rw [W.frobEig _ _ hunr, hpar, _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake hrec hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  rw [← h2, rowEig, h3, satEig_eq _ _ _ hk, hq, h4, Multiset.map_map, Multiset.map_map]
  set c : ℂ := (((R.C.mu0 j).val s.w : ℂˣ) : ℂ)⁻¹ * (((normV s.w : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹ with hc
  have h5 : (Finset.univ.val.map ((fun a : ℂ => a⁻¹ * (((R.C.mu0 j).val s.w : ℂˣ) : ℂ)⁻¹ *
      (((normV s.w : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ fun i => (((α i)⁻¹ : ℂˣ) : ℂ))) =
      (Finset.univ.val.map ((fun b : ℂˣ => (b : ℂ)) ∘ α)).map (c • ·) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, inv_inv, smul_eq_mul, hc]
    ring
  have h6 : hkNorm R j k s.w = c ^ k := by
    rw [hc, mul_pow, inv_pow (_ ^ _), ← pow_mul, mul_comm (D.R.nV / 2)]
    rfl
  rw [h5, ← Multiset.pow_smul_esymm, h6, smul_eq_mul]
  ring
variable {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
theorem eig_of_rational_adjoint (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0)
    (hU : R.toRealDat.LUnif) (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x}
    {In : RatIn D (ratDatR R cG kKs hk)} (h : RatAd Y cG kKs hk In) (W : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : RowSide D)
    {sat : D.what₂.FT → PlE D.host → Multiset ℂ} (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D (typeR Y) (fun σ w => W.e w (Rw.locR σ w)) sat)
    (hsub : In.Sb ⊆ Sb') (hlow : Low D Sb') :
    EigTrue D R.C Rw Sb' In.eig ∧ EigOcc D (ratDatR R cG kKs hk) In.θ In.hL Sb' In.eig :=
  ⟨_root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL Y hlev W Rw hrow h.eig hsub hlow, eigOcc Y hlev hU hW hidem ⟨h.lvl, h.psi⟩ h.eig hsub hlow
    fun j k P α Rr h1 h2 hd => h.hecke j k P α Rr h1 h2 ⟨hd.split, fun e => hd.offS (hsub e), hd.odd, hd.le, hd.elt, hd.reps⟩⟩
end Rows
section AtRows
end AtRows
end GlobalTheory.TwInputs.Eig
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsCusp
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSat
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [_root_.NumberField.IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [_root_.NumberField.IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
include hF in
theorem exists_satake_frobenius_eigenvalues_eq_inv_of_unramified (π : CG E a) (h : IsPlaceOver A w) (hu : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).unr) :
    ∃ B : Multiset ℂˣ, π.HasSat w B ∧ (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).frobEig = B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  have e : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (Quotient.mk _ π) h = _ := _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h
  rw [e] at hu
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hu
  refine ⟨Finset.univ.val.map α, hasSatGL_locRep hσ (GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ _ _).2 ⟨α, rfl, hα⟩)), ?_⟩
  rw [e, _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hα, WD.frobEig_diag, Multiset.map_map]
  rfl
end Local
section Polar
end Polar
section Record
end Record
section True
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [_root_.NumberField.IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [_root_.NumberField.IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
end Local
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC _root_.Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section Record
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {l : ℕ} [Fact l.Prime]
variable {ι : Qbar l ≃+* ℂ}
end Record
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
include hF in
theorem readsCusp_alt : haveI := host_isCMField D.host; ReadsCusp D.naut fun a π => (C.e a π).1 := by
  have := host_isCMField D.host
  refine ⟨fun a _ => Subtype.val_injective.comp (C.e a).injective, fun a π _ => (C.e a π).2, fun a π w _ hu => ?_⟩
  rw [T.frobEig w _ hu, C.loc]
  exact _root_.GlobalTheory.HeightCounting.Blocks.exists_satake_frobenius_eigenvalues_eq_inv_of_unramified hL hF _ _ (by have e := (T.unr w _).1 hu; rwa [C.loc] at e)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalEx
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC _root_.Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
theorem CGTrueT.galEx_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) :
    GalEx D := by
  intro l _ ι a ha π hc hr
  have := host_isCMField D.host
  have hr' : (C.e a π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := _root_.UpperTheory.GalS.exists_aw_alt hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) hr'
  refine ⟨r, h1, h2, ?_⟩
  filter_upwards [eventually_natCast_notMem D.host.E l, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ
  have hu' := (D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu
  have e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
    have hu2 := (T.unr w _).1 hu'
    rw [T.tw, C.loc] at hu2 ⊢
    exact ((h3 w hl _ _).eq_unr hu2).symm
  rw [galPol, T.frobEig w _ hu', e]
  exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ
end GlobalTheory.HeightCounting
section
namespace GlobalTheory.GalAllPlaces
end GlobalTheory.GalAllPlaces
end
section
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MAvGood
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MTwinA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
theorem local_component_class_eq_of_good (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i)
    (sp : SplitPlace D.host.E) (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) (hg : Good (GlobalTheory.LocLanglands.cls σ')) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' := by
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hσ
  have h3' := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q') sp σ' hσ'
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w] at h3
  rw [← P.H.emb i Q', ← D.nbc.embAV_loc i Q' sp.w] at h3'
  rw [he] at h3
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)); obtain ⟨a, ha, ε, hlaws⟩ := hOpn) | obtain ⟨a, ha, ε, -, hlaws⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)
  exact _root_.UpperTheory.One.M.LawsM.inj hlaws _ _ hg (h3.symm.trans h3')
end UpperTheory.One.M
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.One.M.good_cls_of_isLocS_av {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (s : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) s σ) : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ) :=
  GlobalTheory.AVGood.members_good UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz D P.M P.tp.tup P.H.av P.H.level
    (GlobalTheory.AVGood.tameAtG_of_tupTied D P.cf P.tp) i Q s σ hσ
theorem UpperTheory.One.M.cls_eq_of_locV_eq' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E)
    (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' :=
  _root_.UpperTheory.One.M.local_component_class_eq_of_good hL D P i Q Q' sp σ σ' hσ hσ' he (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i Q' sp σ' hσ')
end
section
namespace GlobalTheory.ConjPlaceDual
end GlobalTheory.ConjPlaceDual
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzLoc
section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.IsQgOfOver
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.isQg_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    UpperTheory.One.M.IsQg (w.adicCompletion D.host.E) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have key : Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb w (D.host.g k) hw) := by
    refine GlobalTheory.TypeRec.Model.emb_surjective _ _ _ (fun h => ?_)
      (by
        simpa [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
          (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw))
    have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime k).ne_zero
    have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
      (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
    have := hs w.asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h)
    exact w.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  exact ⟨_, this, RingEquiv.ofBijective _ ⟨RingHom.injective _, key⟩, Formalism.BasicNotions.Examples₂.LocF.emb_cont _ _ hw⟩

end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroLoc

end GlobalTheory.DepthZeroLoc
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame

end GlobalTheory.DepthZeroTame
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise
namespace GlobalTheory.DepthZeroType

end GlobalTheory.DepthZeroType
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroLoc
open GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil in
theorem main_m_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n), (∃ v ∈ GlobalTheory.PRep.fixed π.π (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin n)), v ≠ 0) → UpperTheory.One.M.IsQg (w.adicCompletion D.host.E) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w n π).inePol σ = (X - 1) ^ n := by
  intro _ _ hL D w n π ⟨v, hv, hv0⟩ hq σ hσ
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, _, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  have h0 : fixed π.toIrrRep.ρ (KOne (w.adicCompletion D.host.E) (Fin n)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  have h1 := fixed_ne_bot_of_equiv (equivRep π.toIrrRep) h0
  obtain ⟨m, b, hb, hb'⟩ := haveI := UpperTheory.One.M.charZero_compl w; _root_.UpperTheory.One.M.LawsM.depth H (cls π.toIrrRep) (UpperTheory.One.M.good_of_fixed hq _ h1) h1
  have hd := H.dim (cls π.toIrrRep)
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ
  have hW : Formalism.MainNotions.BlochKatoReduction.IsWild (D.nd.plOm.1 w)
      ((ineIncl (D.nd.plOm.2 w) ⟨σ, hI⟩ : Weil (D.nd.plOm.2 w)) : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) := by
    refine ⟨hI, fun y hy => ?_⟩
    have h2 := hσ y hy
    have h3 : (D.nd.plOm.1 w).valuation y ≠ 0 := by simpa using hy
    have e2 : σ y / y - 1 = (σ y - y) / y := by field_simp
    rw [e2, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h3)] at h2
    exact h2
  show (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (cls π.toIrrRep)).inePol σ = (X - 1) ^ n
  rw [← hb] at hd ⊢
  rw [WD.lpDim_mk] at hd
  rw [WD.inePol_of_mem_Ine _ hI, WD.charPol_mk, hb' _ hW, LinearMap.charpoly_one, hd]
end GlobalTheory.DepthZeroLoc
end
end
section
namespace GlobalTheory.DepthZeroTame
end GlobalTheory.DepthZeroTame
end
section
namespace GlobalTheory.DepthZeroType
end GlobalTheory.DepthZeroType
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlobalArtinReciprocityTrivial
section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Narrow
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem New.typeS (_s : TrivialCondition) (H : IsRecT h rc) : TypeLaw h rc := H.choose_spec.choose_spec.type

end UpperTheory.One.M
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzMatchCut
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker
namespace DiscreteGroups.sglob.DzType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
def NarrowBigAlt : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (k := w.adicCompletion E) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → (n = 1 ∨ 16 * n ^ 2 < g) → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))
end DiscreteGroups.sglob.DzType
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzInertia
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
open DiscreteGroups.sglob.DzType
namespace UpperTheory.Lit.Dz
open GlobalTheory.DepthZeroBridge
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise in
theorem depthZeroInertiaBig_of_narrowBig_m_alt : _root_.DiscreteGroups.sglob.DzType.NarrowBigAlt → GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.Zero.LLC.RecTExists →
    _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt := by
  intro HT HG HL
  intro E Ω _ _ _ _ _ _ g _ A w h rc hrc i hi κ L t ht hTC n hbig σ _ τ P hP hinf
  have hn : 0 < n := hP.2.1.1
  obtain ⟨E', _, _, _, _, _, _, _, w', h', hg0, hg1, hN, ⟨ζ, hζ⟩, hfix⟩ := GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots E Ω g A w h i hi n hn
  let t' : Ω ≃ₐ[E'] Ω := { t with commutes' := fun e => hfix t ht e }
  have htt : ∀ z, t' z = t z := fun _ => rfl
  have hdec : t' • A = A := by
    have h0 : t • A = A := ht.1
    ext z
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    conv_rhs => rw [← h0]
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    rfl
  have ht' : t' ∈ Ine (F := E') A := ⟨hdec, fun z hz => ht.2 z hz⟩
  have hres : AlgEquiv.restrictScalars E t' = t := by ext z; rfl
  obtain ⟨a', ha'⟩ : ∃ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' := by
    exact _root_.UpperTheory.One.M.New.artin HL h'
  obtain ⟨art, hart⟩ := HG E' Ω
  set u := a' (ineIncl h' ⟨t', ht'⟩) with hu_def
  have hu : IsUnitAt w' u := GlobalTheory.T.localArtin_inertia_isUnitAt h' a' ha' ⟨t', ht'⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_integer_approx_unit_adicCompletion w' u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hq : 0 < g ^ n - 1 := by
    have : 2 ≤ g ^ n := le_trans hg2 (Nat.le_self_pow hn.ne' g)
    omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hq
  have hy' : y ^ (normV w' - 1) = algebraMap E' Ω ((((g : ℕ) : 𝓞 E')) : E') := by
    rw [hN, hy]; simp
  obtain ⟨σ', hσ'I, hσ'ab, hσ'v⟩ :=
    GlobalTheory.TameRecip.exists_ine_of_unit HG E' Ω art hart w' A h' ((g : ℕ) : 𝓞 E') hg0 hg1 y hy' u x hu hx
  have hab : toAb E' Ω σ' = toAb E' Ω t' := by
    rw [hσ'ab]; exact ha'.glob art hart _
  have hgE : ((g : ℕ) : E') ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  have hkum := GlobalTheory.T.kummerCharacter_factors_absoluteGaloisAbelianization E' Ω (g ^ n - 1) hq ζ hζ ((g : ℕ) : E') hgE y (by rw [hy, map_natCast]) σ' t' hab
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E' Ω)]; exact (_root_.map_ne_zero _).mpr hgE
  have h1 := hTC n hn y hy
  have h2 : redThrough A κ (algebraMap E' Ω ((x : 𝓞 E') : E')) = L.gen n := by
    rw [← h1]
    have e : t y / y = σ' y / y := by rw [hkum]; rfl
    rw [e]
    exact (redThrough_eq_of_val_sub_lt_one A κ (tameQuot_mem A σ' hq hgΩ hy) hσ'v).symm
  haveI := w'.isMaximal
  letI : Field (𝓞 E' ⧸ w'.asIdeal) := Ideal.Quotient.field _
  have hgK : (((g : ℕ) : 𝓞 E' ⧸ w'.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w'.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hg0
  haveI : CharP (𝓞 E' ⧸ w'.asIdeal) g := (CharP.charP_iff_prime_eq_zero (Fact.out : g.Prime)).mpr hgK
  letI : Algebra (ZMod g) (𝓞 E' ⧸ w'.asIdeal) := ZMod.algebra _ g
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_residueField_embedding_place_over E' Ω g A w' h' κ
  have hcard : Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n := hN
  haveI : Finite (𝓞 E' ⧸ w'.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨θ, hreg, ⟨x0, hx0, hθ⟩, hprod⟩ := GlobalTheory.T.exists_regularCharacter_labelRoot_product g L n hn P hP.1 _ hcard ι
  have hιz : ι (Ideal.Quotient.mk _ x) = L.gen n := by rw [hι]; exact h2
  have hgen0 : L.gen n ≠ 0 := by
    intro e
    have ho := L.gen_order n hn
    rw [e, orderOf_eq_zero_iff'.mpr (fun k hk => by simp [zero_pow hk.ne'])] at ho
    omega
  have hz0 : (Ideal.Quotient.mk w'.asIdeal x) ≠ 0 := by
    intro e; rw [e, map_zero] at hιz; exact hgen0 hιz.symm
  set z : (𝓞 E' ⧸ w'.asIdeal)ˣ := Units.mk0 _ hz0 with hz
  have hform : ∀ y' : Gn g n, Irreducible (y' : Mt g n).charpoly → ∀ z' : (𝓞 E' ⧸ w'.asIdeal)ˣ,
      aeval (z' : 𝓞 E' ⧸ w'.asIdeal) (y' : Mt g n).charpoly = 0 →
      τ.character y' = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z' ^ g ^ j) : ℂˣ) : ℂ) := by
    intro y' hy' z' hz'
    have hmem : ι z' ∈ Formalism.CyclotomicNorms.rootsBar (y' : Mt g n).charpoly := by
      unfold Formalism.CyclotomicNorms.rootsBar
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Matrix.charpoly_monic _).ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have hc : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) = ι.comp (algebraMap (ZMod g) (𝓞 E' ⧸ w'.asIdeal)) :=
        RingHom.ext_zmod _ _
      rw [hc, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hz', map_zero]
    rw [hP.2.2 x0 hx0 y' hy' (ι z') hmem]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hθ, Units.val_pow_eq_pow_val, map_pow]
  have H := HT E E' Ω g A w h w' h' rc hrc i hi n hn hbig hg1 hN a' ha' (𝓞 E' ⧸ w'.asIdeal) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (Ideal.mk_ker) θ hreg τ hP.2.1 hform σ hinf ⟨t', ht'⟩ x z rfl hx
  rw [← hres, H]
  exact hprod z hιz
end UpperTheory.Lit.Dz
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MNarrow
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem narrowBig_alt (s : _root_.UpperTheory.One.M.TrivialCondition) (_art : GlobalTheory.Published.GlobalArtinReciprocity) (_hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.DiscreteGroups.sglob.DzType.NarrowBigAlt :=
  fun _ E' _ _ _ _ _ _ _ _ _ _ _ _ _ g _ _ _ _ w' h' _ H i hi n hn _ h1 h2 a' ha' K _ _ red h3 h4 θ hθ τ hτ h5 σ h6 =>
    (_root_.UpperTheory.One.M.New.typeS s H E' g w' h' i hi n hn h1 h2 a' ha' K red h3 h4 θ hθ τ hτ h5 σ h6).2
end UpperTheory.One.M
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.Lit.Dz
theorem global_artin_reciprocity_trivial (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt :=
  _root_.UpperTheory.Lit.Dz.depthZeroInertiaBig_of_narrowBig_m_alt ((_root_.UpperTheory.One.M.narrowBig_alt trivial) PositivityTheory.Stage1.PM.globalArtinReciprocity hL)
    PositivityTheory.Stage1.PM.globalArtinReciprocity hL
end UpperTheory.Lit.Dz
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicativeClosurePrimeMem
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.Top.Bl.MultQClose
set_option maxHeartbeats 2000000 in
theorem multiplicative_closure_prime_mem_alt : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) := by
  intro h1 h2 h3 h4 h5 h6 h7 h12 h13 h14 hL N S Γ
  refine (GlobalTheory.Fc.EvP.and (GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.R3.LedRec.ev_exists_sizeData)
    (GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).mono ?_
  rintro κ K - ⟨hLed, hHost⟩ q
  obtain ⟨Z', g1', hη, hA⟩ := GlobalTheory.Mem.R3.LedRec.exists_bare h14 (B := q.B) (C := q.w.C) q.Z q.f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, -, -, hpar, -⟩ := hLed (q.w.st Z') q.x.isOver hη hA
  obtain ⟨hhost, -⟩ := hHost (q.w.st Z') q.x.isOver
  have s := GlobalTheory.Mem.R3.LedRec.sameGrp q.x.what₂.grp g1'
  have transfer : GlobalTheory.CuspMult.MultEq (GlobalTheory.Mem.R3.DatCopy.copy Z' s q.x.what₂.r.z).R.toRealDat → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat := by
    intro h
    have e := GlobalTheory.Mem.R3.DatCopy.twice_eq Z' (iK := q.x.what₂.r.z.alg) q.x.what₂.r.z.R
    have h2 := GlobalTheory.Mem.R3.DatCopy.multEq_tr (a := Z') q.Z (iK := GlobalTheory.Mem.R3.Tr.alg Z' q.x.what₂.r.z.alg) (R := GlobalTheory.Mem.R3.Tr.real Z' q.x.what₂.r.z.R.toRealDat)
      (by with_unfolding_all exact h)
    rw [e]
    with_unfolding_all exact h2
  apply transfer
  have hEx' := GlobalTheory.Mem.R3.DatCopy.copy_exAt Z' s q.x.what₂.exAt
  have hok := q.x.what₂.r.intersectionNumber_baseChange.ok
  have hok' : (GlobalTheory.Mem.R3.famR Z'.st q.w.I q.x.what₂.hX (GlobalTheory.Mem.R3.usedOf q.w.I q.T q.x.Wt)
      (GlobalTheory.Mem.R3.DatCopy.copy Z' s q.x.what₂.r.z).Xg (GlobalTheory.Mem.R3.DatCopy.copy Z' s q.x.what₂.r.z).tr).fam3.Ok3 1 := hok
  clear hok
  generalize GlobalTheory.Mem.R3.DatCopy.copy Z' s q.x.what₂.r.z = y at hEx' hok' ⊢
  have hch := y.pins.char
  have hT : TypesTrue (q.w.st Z').toD7.ntypes y.R.C.P y.R.C.W := by
    rw [y.lev.C, q.w.C_eq]
    exact g1'
  exact _root_.GlobalTheory.T.twisted_multiplicity_one h1 h2 h3 h4 h5 h6 h7 h12 h13 h14 y.R y.F (s := 1) hok' hch hEx' hhost ⟨L, hpar⟩ q.B.ccK_top
    y.pins.keep.guard (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev hT)
end GlobalTheory.Mem.Top.Bl.MultQClose
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.member_multiplicatively_closed_alt : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.MultQClose.multiplicative_closure_prime_mem_alt | exact _root_.GlobalTheory.Mem.Top.Bl.MultQClose.multiplicative_closure_prime_mem_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.MultQClose.multiplicative_closure_prime_mem_alt <;> assumption)
end
end
end
