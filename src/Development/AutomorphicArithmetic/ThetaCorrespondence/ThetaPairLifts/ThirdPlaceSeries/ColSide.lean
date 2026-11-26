module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvariance
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DatExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevelWtConst
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPins
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsExists

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomExists
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomExists
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam.KomExist
theorem exists_compactOpen_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
    ∀ t j, j < B.R.m → IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (_root_.GlobalTheory.Fam.chrK_alt W t j) (_root_.GlobalTheory.Fam.chrK_alt W t j) (kom t j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ haT
  have hL := hW.pk.bot.hyp.2.2.2.1.lev
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists (I.rec7 l Z)
  have key : ∀ (t : W.P.T) j, j < B.R.m → ∃ om : Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
      IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (_root_.GlobalTheory.Fam.chrK_alt W t j) (_root_.GlobalTheory.Fam.chrK_alt W t j) om := by
    intro t j hj
    have hH := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t ⟨j, hj⟩
    exact hE _ _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ haT.pinX.std hH hH
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX j (le_of_lt hj)))
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX (j + 1) hj))
  classical
  refine ⟨fun t j => if h : j < B.R.m then (key t j h).choose else 1, fun t j hj => ?_⟩
  simp only [dif_pos hj]
  exact (key t j hj).choose_spec
end GlobalTheory.Fam.KomExist
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomExistsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_exists_kernel_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
    ∀ t j, j < B.R.m → IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (_root_.GlobalTheory.Fam.chrK_alt W t j) (_root_.GlobalTheory.Fam.chrK_alt W t j) (kom t j) := by
  first | exact @_root_.GlobalTheory.Fam.KomExist.exists_compactOpen_alt | exact _root_.GlobalTheory.Fam.KomExist.exists_compactOpen_alt | (intros; apply _root_.GlobalTheory.Fam.KomExist.exists_compactOpen_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QLevOfReads
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevSTopIff
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevSTopIff
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TopLevQ.mem_levS_top_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 t PP hP E x hx g hg
  have hTop : x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J ↔ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k _ ∧ GlobalTheory.StepData.MaxM x.val.toBlocks₂₁ := by
    show x ∈ ((GlobalTheory.StepData.parahoric _ _ E.δ E.tame).toLevel.map (GlobalTheory.StepData.LatFrame.refl _ _).conj).J ↔ _
    rw [GlobalTheory.StepData.Level.mem_map]
    have e1 : (GlobalTheory.StepData.LatFrame.refl (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2))).conj.symm x = x := by
      ext i j
      simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_symm_val]
      rfl
    rw [e1]
    exact GlobalTheory.StepData.mem_parahoric
  rw [hTop]
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frameTop
  have hmv' : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (a.Q PP ⟨t, hP⟩).q) (I.rec7 l Z).sp.X' a.g.bT (_root_.GlobalTheory.Fam.pk_z W).βX
      ((a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm) := hmv
  have hidem : Formalism.L2.NTheta.IsIdemAt (a.Q PP ⟨t, hP⟩).q.e PP := (a.Q PP ⟨t, hP⟩).idem
  have hβX : Formalism.IndefR.Links.IsSDFrame (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX 1 := W.Q.charW.base.lev.βX
  obtain ⟨hGfC, hStIff, hoff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff (I.rec7 l Z) (a.Q PP ⟨t, hP⟩).k (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX
    (_root_.GlobalTheory.Fam.pk_z W).ΛX 1 hβX _ (a.Q PP ⟨t, hP⟩).FT e.symm a.g.bT hmv' g x hg
  obtain ⟨hsupp, hmat⟩ := hg
  have hM : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr * (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm =
      (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm * x.val.submatrix e.symm e.symm := by
    have h1 : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr = (a.Q PP ⟨t, hP⟩).FT.β * x.val * (a.Q PP ⟨t, hP⟩).FT.γ := hmat
    rw [h1]
    exact GlobalTheory.TopLevQ.moved_mat _ _ (a.Q PP ⟨t, hP⟩).FT.γβ _ e
  have hsupp' : Formalism.L2.Theta.SuppAt (a.Q PP ⟨t, hP⟩).q.e _ (a.g.bT⁻¹ * g * a.g.bT) := GlobalTheory.TopLevQ.suppAt_conj g a.g.bT hsupp
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Ranks.r
    omega
  have hPg := (_root_.GlobalTheory.PkFrame.pk_frame_places_alt W hW t PP hP 0 (by change 0 < (I.rec7 l Z).R.m; have := (a.Q PP ⟨t, hP⟩).hs; omega)).2
  have hord := GlobalTheory.TopLevQ.blk_iff e he x.val
  rw [← hr] at hord
  rw [GlobalTheory.TopLevQ.mem_levS_iff]
  have hred := GlobalTheory.TopLevQ.red_eq_zero_iff (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX a.g.bT g _ _ hmv' hM
  constructor
  · rintro ⟨-, ⟨hSt, -, hQt⟩, -⟩
    refine ⟨hx, hord.1 fun i j hij => (hred hSt i j).1 ?_⟩
    exact (hQt PP hP) hij
  · rintro ⟨hx', hmax⟩
    have hSt : Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (_root_.GlobalTheory.Fam.pk_z W).βX := hStIff.2 hx'
    have hone : ∀ PP' : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) →
        Formalism.L2.DIV.redFn (_root_.GlobalTheory.Fam.pk_z W).βX PP' (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 :=
      fun PP' hne => GlobalTheory.SplitOffRed.redFn_eq_one_off (a.Q PP ⟨t, hP⟩).q hidem _ _ _ hsupp' hSt PP' hne
    refine ⟨hGfC, ⟨hSt, fun PP' hPP' => ?_, fun PP' hPP' => ?_⟩, ?_⟩
    · rw [hone PP' (hPg PP' hPP')]
      exact Subgroup.one_mem _
    · by_cases hPe : PP' = PP
      · subst hPe
        intro i j hij
        exact (hred hSt i j).2 (hord.2 hmax i j hij)
      · rw [hone PP' fun hu => hPe (hW.pk.sel PP' PP ⟨t, hPP'⟩ ⟨t, hP⟩ hu)]
        exact Subgroup.one_mem _
    · have h1 : Formalism.L2.DIV.rTup (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 := by
        funext PP'
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (_root_.GlobalTheory.Fam.pk_z W).βX PP'.1 _) = 1
        rw [hone PP'.1 (hPg PP'.1 PP'.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact Subgroup.one_mem _
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevSTopIffStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_scalar_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  exact @_root_.GlobalTheory.TopLevQ.mem_levS_top_iff_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtPlace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtPlace
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
noncomputable section
namespace GlobalTheory.QLevMid
set_option maxHeartbeats 2000000 in
theorem level_at_place_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t PP hP E hRes j d hd hj x hxK
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.pk.bot.hyp.2.2.2.1.lev
  obtain ⟨N, hSD⟩ : ∃ N, IsSDFrame (Yc _ j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) N := ⟨_, hl.βY j hj⟩
  have hPg : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg,
      PP'.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ≠
        PP.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := by
    intro PP' hPP' e
    have hApart := GlobalTheory.StepLifts.places_apart _ hl t
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with hEq | hConj
    · exact Finset.disjoint_left.1 hApart.2 hPP' (hEq ▸ hP)
    · exact hApart.1 PP' hPP' PP (Or.inr hP) (GlobalTheory.GoodPrimes.isConjPl_iff.2 hConj)
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frame j d hd
  have hloc := (a.Q PP ⟨t, hP⟩).gl_loc j d hd x
  obtain ⟨hG, hSt, hOff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  have hRed := GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ (a.Q PP ⟨t, hP⟩).compl _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  obtain ⟨hι, hrep⟩ := GlobalTheory.T.completion_smallIntegers_in_prime_dense _ _ PP _ _ _ (a.Q PP ⟨t, hP⟩).compl (a.Q PP ⟨t, hP⟩).unif
  have hSt' := hSt.2 hxK
  have hQ : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, PP'.under (𝓞 (I.rec7 l Z).host.F) = PP.under (𝓞 (I.rec7 l Z).host.F) → PP' = PP :=
    fun PP' hP' h => hW.pk.sel PP' PP ⟨t, hP'⟩ ⟨t, hP⟩ h
  obtain ⟨hmem, hchi⟩ := GlobalTheory.T.mem_twistPlaceLevel_single_place_character _ _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) (I.rec7 l Z).R.r (I.rec7 l Z).R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) PP hP hPg hQ _ hG hOff
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hC1 := GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel _ _ PP _ hι (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η _ e he x hxK _ (hRed hSt')
  have hC2 := GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet _ _ PP _ hι hrep (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) hRes _ e he x
  rw [← hr] at hC1 hC2
  refine ⟨hmem.trans ⟨fun h => hC1.1 h.2, fun h => ⟨hSt', hC1.2 h⟩⟩, fun hx => ?_⟩
  exact (hchi hSt').trans (congrArg Units.val (hC2 hx _ (hRed hSt') (hC1.2 hx)))
end GlobalTheory.QLevMid
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtPlaceStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  exact @_root_.GlobalTheory.QLevMid.level_at_place_alt_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QLevOfReads
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QLevAt
theorem qLev_of_reads_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ row col (F : QFam a.v ((a.fam row col).t t)) (h : F.r = J.r), F.χ = _root_.GlobalTheory.Fam.chrK_alt W t → (∀ i, HEq (F.Q i) (J.E (Fin.cast h i)).toAt) → _root_.GlobalTheory.Fam.QLevAlt (a.fam row col) F := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t J hJ row col F h hχ hQ
  obtain ⟨χ, r, Q, eqv⟩ := F
  dsimp only at h hχ hQ ⊢
  subst hχ
  obtain rfl : Q = fun i => (J.E (Fin.cast h i)).toAt := funext fun i => eq_of_heq (hQ i)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Equiv.ofBijective (fun i => ⟨J.pl (Fin.cast h i), J.mem _⟩) ⟨?_, ?_⟩, fun i => ?_⟩
    · intro i i' e
      have e' := hJ.inj (congrArg Subtype.val e)
      exact Fin.ext (by simpa using congrArg Fin.val e')
    · rintro ⟨PP, hPP⟩
      obtain ⟨i, hi⟩ := hJ.surj PP hPP
      exact ⟨Fin.cast h.symm i, Subtype.ext (by simp [hi])⟩
    · obtain ⟨ε, hε, h3⟩ := (J.G (Fin.cast h i)).q.above
      exact ⟨(J.G (Fin.cast h i)).idem,
        (GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G (Fin.cast h i)).idem hε h3).symm⟩
  · intro i j d hd hj x hx
    exact _root_.GlobalTheory.T.true_geometry_twist_value_alt W hW u a ha haT t (J.pl (Fin.cast h i)) (J.mem _) (J.E (Fin.cast h i)) (hJ.res _) j d hd hj x hx
  · intro i x hx g hg
    exact _root_.GlobalTheory.T.true_geometry_twist_scalar_alt W hW u a ha haT t (J.pl (Fin.cast h i)) (J.mem _) (J.E (Fin.cast h i)) x hx g hg
end GlobalTheory.QLevAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QLevOfReadsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_quadratic_twist_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ row col (F : QFam a.v ((a.fam row col).t t)) (h : F.r = J.r), F.χ = _root_.GlobalTheory.Fam.chrK_alt W t → (∀ i, HEq (F.Q i) (J.E (Fin.cast h i)).toAt) → _root_.GlobalTheory.Fam.QLevAlt (a.fam row col) F := by
  first | exact @_root_.GlobalTheory.QLevAt.qLev_of_reads_alt | exact _root_.GlobalTheory.QLevAt.qLev_of_reads_alt | (intros; apply _root_.GlobalTheory.QLevAt.qLev_of_reads_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZeroColOf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeroForms
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeroForms
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem zero_forms_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col t (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) ι w c₀, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) c₀ A ι w → (∀ β, A.kb 0 β = TC.kStd X u (B.R.N 0)) → ∀ α, (∀ φ, _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ ∈ ((a.fam row col).t t).Ram 0 ∧ ∀ y, ((a.fam row col).t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) y = (GlobalTheory.Core.Mi.chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ ((I.rec7 l Z).eMu u φ).1 y) ∧ ∀ ψ ∈ ((a.fam row col).t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 row col t Ch₀ A ι w c₀ hP hkb α
  have hr := hP.ram 0 (Nat.zero_le _)
  have hq := hP.rdq 0 (Nat.zero_le _)
  have hl := hP.live
  have hok : I.Ok := hW.tr.ok
  obtain ⟨hpins⟩ := hW.tr.pins
  obtain ⟨hstd⟩ := hW.tr.std
  obtain ⟨l0, -⟩ := hW.tw
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := ha2.pinX.inf
  refine ⟨fun φ => ⟨?_, fun y => ?_⟩, fun ψ hψ => ?_⟩
  · show _ ∈ (col t).Ram 0
    exact (hr _).2 ⟨(GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).1 ((I.rec7 l Z).eMu u φ).2, fun c hc => absurd (hl.first _) hc⟩
  · show (col t).rd 0 α _ y = _
    refine (hq α _ y).trans ?_
    exact GlobalTheory.T.scalarForm_transportedColumn_stepZero_standard I hok hpins l Z _ hstd u (W.P.I.tup t) Ch₀ A hP.is (ι 0 α) (hkb _) _ hθ _ ((I.rec7 l Z).eMu u φ).2 y
  · have h1 : GlobalTheory.AdForm.RamT 0 ψ := ((hr ψ).1 hψ).1
    have h2 : ((I.rec7 l Z).e0Tw u (W.P.I.tup t)).symm ψ ∈ ((I.rec7 l Z).mem u).A.Mram :=
      (GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).2 (by rwa [LinearEquiv.apply_symm_apply])
    obtain ⟨φ, hφ⟩ := EquivLike.surjective ((I.rec7 l Z).eMu u) ⟨_, h2⟩
    refine ⟨φ, ?_⟩
    show ψ = (I.rec7 l Z).e0Tw u (W.P.I.tup t) (((I.rec7 l Z).eMu u) φ).1
    rw [hφ]
    exact (LinearEquiv.apply_symm_apply _ ψ).symm
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeroFormsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_column_entry_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col t (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) ι w c₀, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) c₀ A ι w → (∀ β, A.kb 0 β = TC.kStd X u (B.R.N 0)) → ∀ α, (∀ φ, _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ ∈ ((a.fam row col).t t).Ram 0 ∧ ∀ y, ((a.fam row col).t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) y = (GlobalTheory.Core.Mi.chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ ((I.rec7 l Z).eMu u φ).1 y) ∧ ∀ ψ ∈ ((a.fam row col).t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ := by
  first | exact @_root_.GlobalTheory.Fam.zero_forms_alt | exact _root_.GlobalTheory.Fam.zero_forms_alt | (intros; apply _root_.GlobalTheory.Fam.zero_forms_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZeroColOf
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam
theorem chartZero_colOf_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (S : ∀ t j, GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ), (∀ t α, s t 0 α = 1) →
    (∀ t, ∃ w, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd S s cV cK cP t) a.c₀ (J t).A (J t).ι w) →
    _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd S s cV cK cP)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr J hR row kom dd S s cV cK cP hs hpin t
  obtain ⟨w, hw⟩ := hpin t
  have hstd : ∀ β, (J t).A.kb 0 β = TC.kStd X u (B.R.N 0) :=
    (hR t).std 0 (by have := B.R.two_le_m; omega)
  have key := _root_.GlobalTheory.T.true_geometry_row_column_entry_alt W hW u a ha hTr row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd S s cV cK cP) t (J t).Ch₀ (J t).A (J t).ι w a.c₀ hw hstd
  have hone : ∀ i, Fintype.card (((J t).E i).Ch 0) = 1 ∧ ∀ α, ((J t).E i).wt 0 α = 1 := fun i =>
    let h := GlobalTheory.T.bottom_spherical_card_weight_index _ _ _ _ _ _ _ ((J t).E i)
    ⟨h.1, h.2.1⟩
  have hU : ∀ i, Nonempty (Unique (((J t).E i).Ch 0)) := fun i =>
    (Fintype.card_eq_one_iff_nonempty_unique).1 (hone i).1
  let α₀ : (J t).Ch 0 := fun i => (hU i).some.default
  have hall : ∀ α : (J t).Ch 0, α = α₀ := fun α => funext fun i => (hU i).some.uniq (α i)
  refine ⟨α₀, hall, ?_, ?_⟩
  · show ((s t 0 α₀ • (J t).eps 0 α₀).mapDomain (· * a.g.b 0)) = _
    have hw1 : (J t).wt 0 α₀ = 1 := by
      unfold _root_.GlobalTheory.Fam.QuadraticExtensionData.wt
      exact Finset.prod_eq_one fun i _ => (hone i).2 _
    have he : (J t).eps 0 α₀ = Finsupp.single 1 1 := by
      unfold _root_.GlobalTheory.Fam.QuadraticExtensionData.eps
      rw [if_pos (Or.inr rfl), hw1, one_smul]
      apply conv_single_one_of_forall
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ((J t).E i).εL_zero _
    rw [hs, one_smul, he, Finsupp.mapDomain_single, one_mul]
  · exact key α₀
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZeroColOfStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_bound_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (S : ∀ t j, GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ), (∀ t α, s t 0 α = 1) →
    (∀ t, ∃ w, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd S s cV cK cP t) a.c₀ (J t).A (J t).ι w) →
    _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd S s cV cK cP)) := by
  first | exact @_root_.GlobalTheory.Fam.chartZero_colOf_alt | exact _root_.GlobalTheory.Fam.chartZero_colOf_alt | (intros; apply _root_.GlobalTheory.Fam.chartZero_colOf_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfPinTupCombAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfPinTupCombAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.QPl.PinComb
variable {D : D7} {c : Comm D}
variable {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}
end GlobalTheory.QPl.PinComb
open GlobalTheory.QPl.PinComb in
theorem GlobalTheory.QPl.PinComb.famOf_pinTup_combAt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j,
    GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).dQ j α γ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ J _ row col hCh sc cT t j
  exact pinTup_combAt _ sc cT j
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfPinTupCombAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j,
    GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).dQ j α γ) := by
  first | exact @_root_.GlobalTheory.QPl.PinComb.famOf_pinTup_combAt_alt | exact _root_.GlobalTheory.QPl.PinComb.famOf_pinTup_combAt_alt | (intros; apply _root_.GlobalTheory.QPl.PinComb.famOf_pinTup_combAt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfEpsMem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfEpsMem
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.QPl.EpsSupp
end GlobalTheory.QPl.EpsSupp
open GlobalTheory.QPl.EpsSupp in
theorem GlobalTheory.Fam.famOf_eps_mem_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ J _ row col hCh sc cT t j α g hg
  have h1 := eps_mem_grpAt (_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t) sc cT (fun i β => ((J t).E i).εL_zero β) j α g hg
  refine ⟨h1, mul_mem (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h1) ?_⟩
  rw [← (ha.tie row col).1.b j]
  exact ha.vis.b j
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfEpsMemStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  first | exact @_root_.GlobalTheory.Fam.famOf_eps_mem_alt | exact _root_.GlobalTheory.Fam.famOf_eps_mem_alt | (intros; apply _root_.GlobalTheory.Fam.famOf_eps_mem_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColOfReadS
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColOfReadS
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam
theorem colOf_readS_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ha hat J hJ k
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  choose S hS using fun t => GlobalTheory.T.levelPrimeOperators_act_ramifiedColumns_vanishing I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) _ _ (J t).A (J t).ι (hJ t).is (_root_.GlobalTheory.Fam.pk_z W).θ
    hat.pinX.inf a.k a.ι a.o.p a.o.β a.o.Q (fun j => (a.g.x j).L) hat.std a.o.I a.o.q a.o.χ a.o.hχ
  refine ⟨S, fun t => ⟨fun j hj η φ hφ => ((hS t j hj φ hφ).2 η).1, fun row kom dd s cV cK cP => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j hj ψ hψ α y
    have h := (hS t j hj ψ hψ).1 ((J t).ι j α) y
    change (if hj' : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj' ((J t).ι j α) ψ y else 0) ∈ a.o.Ram j
    have hj2 : j ≤ B.R.m := hj
    rw [dite_eq_left hj2]
    exact h
  · intro j hj ψ hψ α y
    have hj' : j ≤ B.R.m := by change j + 2 ≤ B.R.m at hj; omega
    change (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) (S t j (k.ε j) ψ) y else 0) =
      a.o.S k.ε j (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) ψ y else 0)
    rw [dite_eq_left hj', dite_eq_left hj']
    exact ((hS t j hj' ψ hψ).2 (k.ε j)).2 _ y
  · intro η ψ hψ
    have h0 : (0 : ℕ) ≤ B.R.m := Nat.zero_le _
    refine ⟨((hS t 0 h0 ψ hψ).2 η).1, fun α y => ?_⟩
    change (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) (S t 0 η ψ) y else 0) =
      a.o.S (fun _ => η) 0 (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) ψ y else 0)
    rw [dite_eq_left h0, dite_eq_left h0]
    exact ((hS t 0 h0 ψ hψ).2 η).2 _ y
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColOfReadSStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  first | exact @_root_.GlobalTheory.Fam.colOf_readS_alt | exact _root_.GlobalTheory.Fam.colOf_readS_alt | (intros; apply _root_.GlobalTheory.Fam.colOf_readS_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsSide
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsSide
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam.FinData
theorem main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (s : ∀ j, J.Ch j → ℂ) j α γ, j < B.R.m →
    GlobalTheory.SeeSaw.IsFinComb (J.dQ s j α γ) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dG j) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dT j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ t J _ s j α γ hj
  refine ⟨?_, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atG j).2.1, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atT j).1⟩
  unfold _root_.GlobalTheory.Fam.QuadraticExtensionData.dQ
  refine isFinComb_smul _ _ (isFinComb_smul _ _ (GlobalTheory.QPl.ThetaPin.isFinComb_aconv _ fun e he => ?_))
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  obtain ⟨ε, hε, hsum⟩ := (J.G i).q.above
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  refine GlobalTheory.QPl.ThetaPin.isFinComb_of_half hε _ fun w hw => hsum ▸ ?_
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  rcases Nat.lt_or_ge j (J.G i).s with h1 | h1
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = (J.G i).s := ⟨(J.G i).s - j - 1, by omega⟩
    exact ((J.E i).dL_mid j d hd (α i) (γ i)).1 w hw
  · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · subst h2
      exact ((J.E i).dL_pen (α i) (γ i)).1 w hw
    · obtain rfl : j = (J.G i).s + 1 := by omega
      exact ((J.E i).dL_top (α i) (γ i)).1 w hw
end GlobalTheory.Fam.FinData
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsSideStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_local_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (s : ∀ j, J.Ch j → ℂ) j α γ, j < B.R.m →
    GlobalTheory.SeeSaw.IsFinComb (J.dQ s j α γ) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dG j) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dT j) := by
  first | exact @_root_.GlobalTheory.Fam.FinData.main_alt_alt | exact _root_.GlobalTheory.Fam.FinData.main_alt_alt | (intros; apply _root_.GlobalTheory.Fam.FinData.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColSide
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
theorem GlobalTheory.Fam.colSide_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a) row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (a := a) k (row := row) (col := col) w₀ w F := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hiA k row hrow hsame
  classical
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  have hc : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row _root_.GlobalTheory.Fam.trivialColumnChoice) (hRow _)).1
  choose J hJ using _root_.GlobalTheory.T.exists_quadratic_extension_reads_of_true W hW u a ha haT hc
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt_alt W hW u a ha haT hiA
  choose s ζ ρ hD using fun t => hC t (J t) (hJ t)
  obtain ⟨V, VT, hV0, hVT0, hV⟩ := _root_.GlobalTheory.T.true_geometry_exists_volume_data_alt W hW u a ha haT
  obtain ⟨kom, hkom⟩ := _root_.GlobalTheory.T.true_geometry_exists_kernel_alt W hW u a ha haT
  have hdd0 : ∀ t j α γ, ∃ d, j < B.R.m → GlobalTheory.SeeSaw.IsFinComb d ∧ ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d f =
      comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((J t).dQ (s t) j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) f)) := by
    intro t j α γ
    by_cases hj : j < B.R.m
    · obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_twist_local_value_alt W hW u a ha haT t (J t) (hJ t) (s t) j α γ hj
      obtain ⟨d, hd⟩ := GlobalTheory.Fam.finComb3 _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ _ _ _ h1 h2 h3
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose dd hdd using hdd0
  obtain ⟨S', hS'⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_relation_alt W hW u a ha haT J hJ k
  have hone : ∀ t, ∃ β₀ : (J t).Ch B.R.m, ∀ β, β = β₀ := fun t => by
    have hc1 : Fintype.card ((J t).Ch B.R.m) = 1 := by
      rw [Fintype.card_pi]
      refine Finset.prod_eq_one fun i _ => ?_
      have h1 := ((J t).E i).one
      have h2 : ((J t).G i).s + 1 + 1 = B.R.m := ((J t).G i).hs
      rw [h2] at h1
      exact h1
    exact Fintype.card_eq_one_iff.1 hc1
  choose β₀ hβ₀ using hone
  let cQf : W.P.T → ℕ → ℂ := fun t j => ∏ i, ((((J t).E i).idx (j + 1) : ℂ) * (((J t).E i).idx (j + 1 + 1) : ℂ))⁻¹
  let cTf : W.P.T → ℕ → ℂ := fun t j => @TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j) ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
  let cK : W.P.T → ℕ → ℂ := fun t j => V j * C j * a.c₀ j * ρ t j
  let cP : W.P.T → ℂ := fun t => VT * ∑ β, s t B.R.m β
  let cV : W.P.T → ℕ → ℂ := fun t j => if h : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then
      k.v.kap j h.choose h.choose_spec * (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
    else (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
  let col := _root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP
  let F := _root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col (fun _ => rfl)
  let w₀ := fun t => (F t).pinTup (k.sc t) (cTf t)
  let w := fun t => GlobalTheory.QTw.resc (w₀ t) (s t)
  have hPinCh : ∀ t, ∃ w, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) a.c₀ (J t).A (J t).ι w := fun t => by
    refine ⟨fun j α γ => C j * (J t).wt j α * ζ t j α γ, ?_⟩
    refine
      { is := (hJ t).is
        live := (hJ t).live
        om := fun j hj => by rw [(hJ t).chr j hj]; exact hkom t j hj
        dat := fun j hj α γ => ⟨(hdd t j α γ (by omega)).1, by
          show IsRatDatum _ _ _ _ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (dd t j α γ) (a.g.vac j))
          rw [(hdd t j α γ (by omega)).2]
          exact ((hD t).2.2.2 j hj α γ).1⟩
        cst := fun j hj α γ _ => by
          have h1 := ((hV t (J t) (hJ t)).1 j (by omega) α)
          have h2 := ((hD t).2.2.2 j hj α γ).2
          show V j * C j * a.c₀ j * ρ t j = _
          rw [← h1, ← h2]
          ring
        ram := fun j _ φ => Iff.rfl
        rdq := fun j hj β φ y => dif_pos hj }
  refine ⟨col, w₀, w, F, ⟨a.c₀, haT.pinX, fun t => ⟨⟨(J t).Ch₀, (J t).A, (J t).ι, hPinCh t⟩, ?_⟩⟩, ?_⟩
  · obtain ⟨UT, hUT1, hUT2⟩ := (hV t (J t) (hJ t)).2
    refine ⟨UT, s t B.R.m (β₀ t) * (J t).wt B.R.m (β₀ t),
      { emb := haT.emb
        lev := hUT1
        eT := fun n h β => ?_
        cP := ?_ }⟩
    · subst h
      rw [hβ₀ t β]
      show (s t B.R.m (β₀ t) • Finsupp.single (1 : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') ((J t).wt B.R.m (β₀ t))).mapDomain (· * a.g.bT) = _
      rw [Finsupp.smul_single, Finsupp.mapDomain_single, one_mul, smul_eq_mul]
    · show VT * ∑ β, s t B.R.m β = _
      rw [Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb), ← hUT2 (β₀ t)]
      ring
  have hdQ : ∀ t j α γ, j < B.R.m → (w t).dQ j α γ = (J t).dQ (s t) j α γ := fun t j α γ hj => by
    show _ • (if j < B.R.m then _ else 0) = _
    rw [if_pos hj]
    rfl
  have hpl := fun t => _root_.GlobalTheory.T.true_geometry_twist_local_data_alt W hW u a ha haT t (J t) (hJ t)
  have hQ : ∀ t p, p ∈ (w₀ t).Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := fun t p => by
    show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, (hpl t).2 i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, hi⟩ := (hJ t).surj PP hPP
      exact ⟨i, Finset.mem_univ _, by rw [(hpl t).2 i, hi]⟩
  have hPins : ∀ t, (F t).Pins (w₀ t) := fun t =>
    { inj := (hpl t).1
      places := fun p => by
        show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
        rw [Finset.mem_image]
        exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
      kom := fun j hj => hkom t j hj
      mid := fun j σ h => ⟨(_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, ((hrow t).sBF j (σ + 1) h).2.2.1, ((hrow t).sBF j (σ + 1) h).2.2.2,
        ((hrow t).sFB j σ h).2.2.1, ((hrow t).sFB j σ h).2.2.2⟩
      lastc := fun j h => ((hrow t).sBF j 0 h).2.2.2
      eQ := fun j hj => if_pos hj
      eQT := fun j h => rfl
      dQ := fun j hj α γ => if_pos hj
      ε := fun j ρ' h α => if_pos (Or.inl ⟨ρ', h⟩)
      εT := fun n h β => rfl
      FY := fun j _ f hf => hf
      cQ := fun j _ => rfl }
  have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
    have h1 := ha.vis.bT
    rw [((ha.tie row col).1.bT).1] at h1
    exact h1
  have hOK : (a.fam row col).ColOK :=
    { kom := fun t j hj => hkom t j hj
      ker := fun t j hj α γ => by
        have hx := haT.pinX.xs j (by omega)
        have hx' := haT.pinX.xs (j + 1) (by omega)
        have hL : ((a.g.x j).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx.2.2 z)
        have hL' : ((a.g.x (j + 1)).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx'.2.2 z)
        have hv : IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ (a.g.x j).s (a.g.x (j + 1)).s ((a.g.x j).L : Set _)
            ((a.g.x (j + 1)).L : Set _) (a.g.vac j) := by
          rw [hx.1, hx'.1, hL, hL']
          exact haT.pinX.vc j hj
        exact ⟨⟨_, _, hkom t j hj⟩, hv, (hdd t j α γ hj).1⟩
      e := fun t j α g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        exact (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α x (Finsupp.support_smul hx)).2
      eT := fun t n h β g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        have : x = 1 := by
          exact Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hx))
        subst this
        simpa using hbT
      stabK := fun t j hj ψ hψ => GlobalTheory.T.chainKernel_preserves_ramifiedForms_liveCharts I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) (J t).Ch₀ (J t).Ch (J t).A (J t).ι
        (hJ t).is (hJ t).live j hj ψ hψ
      stabS := fun t j hj ψ hψ => (hS' t).1 j hj (k.ε j) ψ hψ }
  have hcv : ∀ t, CVEq k.v (w t) := fun t => by
    refine ⟨fun j σ h => ?_, fun j h => ?_⟩
    · have hex : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := ⟨σ, h⟩
      have hk : ∀ σ' (h' : j + 2 * (σ' + 1) + 2 = B.R.m), k.v.kap j σ' h' = k.v.kap j σ h := fun σ' h' => by
        obtain rfl : σ' = σ := by omega
        rfl
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dif_pos hex, hk]
      rfl
    · have hex : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := fun ⟨σ, h'⟩ => by omega
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dite_eq_right hex]
      rfl
  have hroot : ∀ (Sp : ℕ → Prop) (x : ℂ), (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → ∀ y : ℂ, (∃ n : ℕ, 0 < n ∧ y ^ n = 1) → ∀ c : ℂ, c ≠ 0 →
      GlobalTheory.Fam.UnitRatio Sp (c * x) (c * y) := fun Sp x ⟨n1, hn1, hx⟩ y ⟨n2, hn2, hy⟩ c hc => by
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hy
      exact zero_ne_one hy
    refine (GlobalTheory.Fam.unitRatio_laws Sp).2.2.1 _ _ (n1 * n2) (mul_ne_zero hc hy0) (Nat.mul_pos hn1 hn2) ?_
    rw [mul_pow, mul_pow, pow_mul x, hx, pow_mul' y, hy, one_pow, one_pow]
  have hsum : ∀ t, ∑ β, s t B.R.m β = s t B.R.m (β₀ t) := fun t =>
    Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb)
  refine
    { ok := hOK
      pins := hPins
      same := fun t => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      laws := fun t => _root_.GlobalTheory.T.true_geometry_family_final_alt hDS hHC W hW u a ha haT row col (hRow col) hOK t (F t) (w₀ t) (s t) (hD t).1 (hPins t) (hQ t)
      lev := fun t => _root_.GlobalTheory.T.true_geometry_quadratic_twist_level_alt W hW u a ha haT t (J t) (hJ t) row col (F t) rfl rfl (fun i => HEq.rfl)
      vec := fun t => _root_.GlobalTheory.T.true_geometry_joint_twist_identity_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) _ t
      FY := fun t j f => Iff.rfl
      FT := fun t f => Set.mem_univ f
      FX := fun t j _ ψ _ α y => Set.mem_univ _
      atQ := fun t j => by
        obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_value_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j
        refine ⟨h1, h2, fun α γ x hx => h3 α γ x (Finsupp.support_smul hx)⟩
      e := fun t j α => ⟨rfl, fun g hg => (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α g (Finsupp.support_smul hg)).1⟩
      eT := fun t n h β => ⟨rfl, fun g hg => by
        have hg' := Finsupp.support_single_subset (Finsupp.support_smul hg)
        rw [Finset.mem_singleton.1 hg']
        exact Subgroup.one_mem _⟩
      dd := fun t j hj α γ f _ => by
        rw [hdQ t j α γ hj]
        exact (hdd t j α γ hj).2 f
      read := fun t => ⟨S' t 0, (hS' t).2 row kom dd s cV cK cP⟩
      sc := fun t => rfl
      cT := fun t j ρ' h => (congrArg (@TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j)) ((hrow t).sBF j ρ' h).2.2.2).symm
      cv := hcv
      cK := fun t j hj => hroot _ _ ((hD t).2.2.1 j) _ ((hD _).2.2.1 j) _
        (mul_ne_zero (mul_ne_zero (hV0 j hj) (hC0 j hj)) (haT.pinX.mv j (by omega)).1)
      cP := fun t => by
        show GlobalTheory.Fam.UnitRatio _ (VT * ∑ β, s t B.R.m β) (VT * ∑ β, s _ B.R.m β)
        rw [hsum, hsum]
        exact hroot _ _ ((hD t).1 _ _) _ ((hD _).1 _ _) _ hVT0
      zero := _root_.GlobalTheory.T.true_geometry_joint_twist_bound_alt W hW u a ha haT J hJ row kom dd _ s cV cK cP (fun t α => (hD t).2.1 α) hPinCh }
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColSideStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_family_invariance_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a) row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (a := a) k (row := row) (col := col) w₀ w F := by
  first | exact @_root_.GlobalTheory.Fam.colSide_alt | exact _root_.GlobalTheory.Fam.colSide_alt | (intros; apply _root_.GlobalTheory.Fam.colSide_alt <;> assumption)
end
end
