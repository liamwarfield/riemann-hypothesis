module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimRows3OfParts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibility
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeClose
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateBaseLevelOfHoweUnramifiedCorrespondence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarPosAllPlacesOfConjugateIdentity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsPassToMovedDivisionLatticesHeights

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputs
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.AtDatumEvaluation

open GlobalTheory.Mem.Top.GroupRetwisting

theorem ev_scale {p : ℝ → ℝ → Prop} (h : ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, p eps x₀) :
    Ev fun K => ∃ x₀ : ℝ, x₀ ≤ K.s.x ∧ p K.s.eps x₀ :=
  ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    let ⟨x₀, hx⟩ := h eps h0
    ⟨x₀, fun _ _ _ _ hs hx' => ⟨x₀, hx', hs ▸ hx⟩⟩⟩⟩⟩⟩

theorem serClause_of_typesTrue (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) {P : Formalism.L2.Host.PiBar D.host} {W : Formalism.L2.Host.Omg D.host}
    (hT : TypesTrue D.ntypes P W) : SerClause D := by
  intro k
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hζ : Formalism.L2.NT.IsGenSys (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro d hd
    refine ⟨(GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order d hd, fun d' hdd hd' => ?_⟩
    obtain ⟨e, rfl⟩ := hdd
    exact (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_norm d e hd (Nat.pos_of_mul_pos_left hd')
  obtain ⟨O, -, -, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
    (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen hζ)
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact ⟨_, O, fun f => (hT.ser k f).trans (GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG _ _ _ _ _ (hT.teich k) O hO D.R.r f hr)⟩


end GlobalTheory.Mem.R3.Rw.AtDatumEvaluation

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

theorem kept_trans_layer {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''} (h : Kept c c') (h' : Kept c' c'') :
    Kept c c'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.forms.Fm.trans h'.forms.Fm, h.forms.acgFm.trans h'.forms.acgFm, h.forms.modFmK.trans h'.forms.modFmK, h.forms.modFmO.trans h'.forms.modFmO, h.forms.actG.trans h'.forms.actG, h.forms.U.trans h'.forms.U, h.forms.psiU.trans h'.forms.psiU, h.forms.eAlg.trans h'.forms.eAlg, h.forms.Dat.trans h'.forms.Dat, h.forms.th.trans h'.forms.th, h.forms.lev.trans h'.forms.lev, h.forms.thPsi.trans h'.forms.thPsi, h.forms.MtV.trans h'.forms.MtV, h.forms.acgMt.trans h'.forms.acgMt, h.forms.modMtK.trans h'.forms.modMtK, h.forms.modMtO.trans h'.forms.modMtO, h.forms.MtLat.trans h'.forms.MtLat, h.forms.thP.trans h'.forms.thP, h.forms.hkF.trans h'.forms.hkF⟩,
    h.br.trans h'.br, h.twI.trans h'.twI, h.sd.trans h'.sd, h.Q.trans h'.Q, h.k.trans h'.k, h.psi.trans h'.psi⟩


end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PositionStageMovesGeometric
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 4000000

theorem kept_trans {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''}
    (h : Kept c c') (h' : Kept c' c'') : Kept c c'' := by
  obtain ⟨g1, s1, f1, b1, t1, d1, q1, k1, p1⟩ := h
  obtain ⟨g2, s2, f2, b2, t2, d2, q2, k2, p2⟩ := h'
  refine ⟨?_, ?_, ?_, b1.trans b2, t1.trans t2, d1.trans d2, q1.trans q2, k1.trans k2, p1.trans p2⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := g1
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := g2
    exact ⟨a1.trans e1, a2.trans e2, a3.trans e3, a4.trans e4, a5.trans e5, a6.trans e6, a7.trans e7, a8.trans e8⟩
  · cases s1; cases s2; constructor <;> (apply HEq.trans <;> assumption)
  · cases f1; cases f2; constructor <;> (apply HEq.trans <;> assumption)

end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowPartNeBotPositiveDimension
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn GlobalTheory.LiftRows
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LiftsOnly

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

section Real

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 800000 in
theorem carries_of_upInj (hCusp : GlobalTheory.Published.CuspRapidDecay) (hHowe : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}
    (hOk : A3.fam3.Ok3 s) (hCW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hJ : GlobalTheory.Hk3.InertJunk A3) (hPG : R.PGEquiv F)
    (hUp : UpInj R.toRealDat) : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c := by
  intro c hc
  have hLI := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCusp D
  have hSch : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat
  have hTw := GlobalTheory.VmTwo.twoSided_goodInert hHowe R F hLI hCW hEx hSch
  have hHk := (GlobalTheory.Hk3.inertJunk_iff A3).1 hJ
  obtain ⟨Tc, hTc, hx⟩ := GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hc
  have hne : LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := fun h => hw0 (hUp A3.A.μ0 (h.trans (map_zero _).symm))
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := GlobalTheory.Div.exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  exact ⟨p, hc, GlobalTheory.Div.map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

theorem exists_rowPart_ne_bot_positiveDimension (hCusp : GlobalTheory.Published.CuspRapidDecay) (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hcar : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) (hN : RowsNe R.toRealDat F.lv2) :
    ∃ p, R.EEp3 p ≠ ⊥ := by
  by_contra hne
  push_neg at hne
  have hc0 : ∀ c, R.EEc c = ⊥ := by
    intro c
    by_contra h
    obtain ⟨p, hp⟩ := hcar c h
    have hle : R.EEc c ≤ R.EEp3 p := by
      unfold RealDat3.EEp3
      exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl
    rw [hne p, le_bot_iff] at hle
    exact h hle
  obtain ⟨hCore, hSF, hEq, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  obtain ⟨h, -, -, htop, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) R.SF hSF
  have hbot : (⊤ : Submodule ℂ R.HE.H) = ⊥ := by
    rw [← htop]
    simp only [← hEq, hc0, iSup_bot]
  have hzero : ∀ x : R.HE.H, x = 0 := fun x => by
    have hx : x ∈ (⊤ : Submodule ℂ R.HE.H) := Submodule.mem_top
    rw [hbot] at hx
    exact (Submodule.mem_bot ℂ).1 hx
  obtain ⟨u, hu0, -⟩ := GlobalTheory.RowsPosRed.exists_row R F hC.base.models hN false
  exact hu0 (hzero (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) u))

theorem levW_of_span (hCusp : GlobalTheory.Published.CuspRapidDecay) (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}
    (hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hGS : GoodStable A3.A.X) (hCD : GlobalTheory.CuspMult.CuspDecomp D)
    (hME : GlobalTheory.CuspMult.MultEq R.toRealDat) (hBlock : (R.toCx3 F).zs.InBlock) (hCar : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c)
    (hScal : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) (hA : R.PThmA) (hLT : Formalism.IndefR.Rat.LiftTest (R.toCx3 F))
    (hU : R.toRealDat.LUnif) : R.PLevW F := by
  have hSchur := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat
  have hSpan := GlobalTheory.T.cuspidal_multiplicity_carriers R F hOk hC hEx hSchur hGS hCD hME hCar
  have hW := GlobalTheory.T.principalFormsSubspace_eq_good_forms R F hOk hC hEx hSpan hScal hA hLT hBlock
  intro j
  exact (GlobalTheory.T.range_goodProjector_baseLevel_twistedModel R F hOk hC hEx hU j).trans (congrArg (· ⊓ _) (hW j).symm)

theorem partsW_of_carried (hCRD : GlobalTheory.Published.CuspRapidDecay) (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}
    (hOk : A3.fam3.Ok3 s) (hW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hGS : GoodStable A3.A.X) (hCD : GlobalTheory.CuspMult.CuspDecomp D)
    (hME : GlobalTheory.CuspMult.MultEq R.toRealDat) (hOkH : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint)
    (hcar : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) (hkap : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) (hB : R.PThmB)
    (hU : R.toRealDat.LUnif) : (R.toCx3 F).PartsW false := by
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  obtain ⟨hCore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hspan := GlobalTheory.T.cuspidal_multiplicity_carriers R F hOk hW hEx hS hGS hCD hME hcar
  have horth := GlobalTheory.T.W_forms_parts_of_distinct_types_orthogonal R F hOk hW hEx hS hOkH hkap hB
  intro j
  have htype := GlobalTheory.T.range_goodProjector_baseLevel_twistedModel R F hOk hW hEx hU j
  refine ⟨fun p q hpq w hw w' hw' => ?_, ?_⟩
  · exact GlobalTheory.SumW.inner_tw_eq_zero (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) w w'
      (horth j p q hpq _ hw.1 _ hw'.1)
  · obtain ⟨-, -, -, -, -, hst, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hS hirr R.SF hSF j
    have hstab : ∀ p g, (R.Wp3 j p).map (R.gW j (sg0 D A3.A) g) ≤ R.Wp3 j p := by
      intro p g
      unfold RealDat3.Wp3
      simp only [Submodule.map_iSup]
      exact iSup₂_mono fun c _ => by rw [hWc]; exact hst c g
    have hstabX : ∀ p g, ((R.toCx3 F).Wp j p).map (R.gWx F j g) ≤ (R.toCx3 F).Wp j p := by
      rintro p g _ ⟨y, hy, rfl⟩
      exact hstab p g (Submodule.mem_map_of_mem hy)
    have hsumX : (⨆ p, (R.toCx3 F).Wp j p) =
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat j)) :=
      (GlobalTheory.SumW.tw_sub_iSup (twAt D.what₂.embLL A3.A.v0) (R.Wp3 j)).symm.trans
        (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (hspan j))
    rw [htype]
    unfold typeSubspace
    exact GlobalTheory.SumW.iSup_inf_inf_typeSp _ (R.gWx F j) F.P0 F.ψ0⁻¹ ((R.toCx3 F).Wp j) _ hstabX hsumX

end Real


end GlobalTheory.LiftsOnly

end
end
