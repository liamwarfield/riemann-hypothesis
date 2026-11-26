module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealGroupInputsCombined
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExists

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesLiftData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.PrimBase
theorem base_of_ties_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  intro hP D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  have hGiv : GlobalTheory.LiftRows.Given R.toRealDat F.lv2 :=
    GlobalTheory.GivenOfTop.given_of_top R F hT.ok hT.char hT.ex hT.host hT.params hT.ccK hT.guard hT.types
  have hStab : GoodStable A3.A.X := GlobalTheory.T.goodCharacters_dual_stable_of_thetaLift_scalars hP.q12 R.toRealDat F.lv2 hGiv
  have hCD : GlobalTheory.CuspMult.CuspDecomp D := GlobalTheory.CuspDec.cuspDecomp hP.q3 hP.q2 D
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP.q2 D
  have hCore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : GlobalTheory.Hk3.SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 R.toRealDat
  have hTR : GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF :=
    GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq R.toRealDat F.lv2 1 hT.ok.ok2 hCore.1 hSch hStab hCD hM R.SF hCore.2.1
  have hFix : ∀ t P, GlobalTheory.Hk3.Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R.toRealDat t P :=
    GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex
  have hU := GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective hP.q5 hP.q3 hP.q4 hP.q6 hP.q2 hP.q1 hP.q7 hP.q8
    (_root_.ResidueKilled.sec_of_dm hP.q9) hP.q10 hP.q11 R.toRealDat F.lv2 hGiv hT.ccK
    hT.char.allPl hFix R.SF hCore.2.1 hTR
  exact ⟨hGiv, hStab, hCD, hLI, hTR, hU.2.2.1, hU.2.2.2⟩
end GlobalTheory.PrimBase
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_data_of_multiplicity_one : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  first | exact @_root_.GlobalTheory.PrimBase.base_of_ties_alt | exact _root_.GlobalTheory.PrimBase.base_of_ties_alt | (intros; apply _root_.GlobalTheory.PrimBase.base_of_ties_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealGroupInputsCombined
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.RL.LamLinked
set_option maxHeartbeats 2000000 in
theorem isotRank_of_wit_alt (h1 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h2 : GlobalTheory.Published.DiscreteSeriesExists)
    (h3 : GlobalTheory.Published.HarishChandraFinite) (h4 : GlobalTheory.Published.CuspRapidDecay)
    (a1 : GlobalTheory.Published.HarishChandraAnalyticity) (a2 : GlobalTheory.Published.DiscreteSeriesClassification) (a5 : GlobalTheory.Published.CuspTraceClass)
    (a6 : GlobalTheory.Published.DixmierMalliavinFactorisation) (a7 : GlobalTheory.Published.FlathFactorisation)
    (a12 : GlobalTheory.Published.ZelevinskyPolynomialRing) (a13 : GlobalTheory.Published.GeometricLemma) (hG : GlobalTheory.Published.GreenCuspidal)
    {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (hH : Formalism.IndefR.Links.HostHyp (q.w.st q.Z).toD7)
    (hp : ∃ L : SizeData₂ (q.w.st q.Z).toD7, Nonempty (ParameterChoice' (q.w.st q.Z).toD7 L)) :
    Formalism.BasicNotions.Rows.IsotRank (q.w.st q.Z).toD7.what₂ := by
  have hGS : Formalism.L2.DIV.GoodStable q.x.what₂.r.z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (q.w.st q.Z).toD7) q.x.what₂.grp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (q.w.st q.Z).B.embLL q.x.what₂.r.z.Xg q.x.what₂.r.z.good.irr fun g => ?_
    apply (q.w.st q.Z).B.embLL.injective
    rw [q.x.what₂.r.z.good.2, q.x.what₂.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (q.w.st q.Z).toD7.ntypes q.x.what₂.r.z.R.C.P q.x.what₂.r.z.R.C.W := by
    rw [q.x.what₂.r.z.lev.C, q.w.C_eq]
    exact q.x.what₂.grp
  have hME := _root_.GlobalTheory.T.twisted_multiplicity_one a1 a2 h4 h3 a5 a6 a7 a12 a13 hG q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
    q.x.what₂.r.z.pins.char q.x.what₂.exAt hH hp q.B.ccK_top q.x.what₂.r.z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue q.x.what₂.r.z.pins.char.base.lev hT)
  exact GlobalTheory.Mem.R3.isotRank_of_multEq h1 h2 h3 h4 _ _ _ _ _ _ _ q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG _ q.x.what₂.r.Y q.x.what₂.r.z.pins
    q.x.what₂.r.intersectionNumber_baseChange hH hGS (GlobalTheory.CuspDec.cuspDecomp h3 h4 _) hME
end GlobalTheory.Fc.RL.LamLinked
namespace GlobalTheory.Fc.RL
end GlobalTheory.Fc.RL
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalMultiplicityEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.Rw.MultAt
open GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 2000000 in
theorem twisted_local_multiplicity_eq : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation →
    GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing →
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal →
    AtDat fun _ _ _ _ _ _ _ _ z => GlobalTheory.CuspMult.MultEq z.R.toRealDat := by
  intro h1 h2 h3 h4 h5 h6 h7 h12 h13 hG
  have e1 := (evG_of_ev LedRec.ev_exists_sizeData).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  refine s1.trans (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨hLed, hHost⟩ B f T hO - - hOk w hw Z hX Wt z g1 g2 hEx g4
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hG (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz, hpar, hn⟩ := hLed (w.st Z') hO hη hA
  obtain ⟨hhost, -⟩ := hHost (w.st Z') hO
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  have hMult : GlobalTheory.CuspMult.MultEq (DatCopy.copy Z' s z).R.toRealDat := by
    have hEx' := DatCopy.copy_exAt Z' s hEx
    generalize DatCopy.copy Z' s z = y at hEx' ⊢
    have hch := y.pins.char
    have hT : TypesTrue (w.st Z').toD7.ntypes y.R.C.P y.R.C.W := by
      rw [y.lev.C, w.C_eq]
      exact g1'
    exact _root_.GlobalTheory.T.twisted_multiplicity_one h1 h2 h3 h4 h5 h6 h7 h12 h13 hG y.R y.F
      ((hOk w.px w.I hX w.ok w.C_eq w.xi_range).2 _ y.Xg y.tr y.good.irr) hch hEx' hhost ⟨L, hpar⟩ B.ccK_top
      y.pins.keep.guard (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev hT)
  exact (GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer
    B w.C Z Z' w.px w.I hX T Wt s z).1 hMult
end GlobalTheory.Mem.R3.Rw.MultAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaParameterDictionaryBijective
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopDict
open Matrix
theorem theta_parameter_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j X hG hX A A₁ AV AV₁ hA hA₁ hAV hAV₁
  exact dict_frames X _ _ _ _ _ _ hX.2.2.2.2.2.2.2 A A₁ (frSum AV AV₁)
    (hG.2.2.2.1.trans (funext fun τ => (hA τ).2.symm)) (hG.2.2.2.2.1.trans (funext fun τ => (hA₁ τ).2.symm))
    (hG.2.2.2.2.2 AV AV₁ hAV hAV₁)
end GlobalTheory.TopDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_parameter_dictionary_bijective : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  first | exact @_root_.GlobalTheory.TopDict.theta_parameter_dictionary | exact _root_.GlobalTheory.TopDict.theta_parameter_dictionary | (intros; apply _root_.GlobalTheory.TopDict.theta_parameter_dictionary <;> assumption)
end
end
