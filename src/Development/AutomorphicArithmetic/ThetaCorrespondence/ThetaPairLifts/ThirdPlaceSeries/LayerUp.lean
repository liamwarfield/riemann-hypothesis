module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def Mv.sideA_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding m.D (m.cf cf) jE := @_root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding.mk (_) (_) (_)
    (bare := (by with_unfolding_all exact (A.bare :)))
    (wdT := (by with_unfolding_all exact (A.wdT :)))
    (lab := (by with_unfolding_all exact (A.lab :)))
    (chr := @_root_.GlobalTheory.HeightCounting.CharSide.mk (_) (_)
      (e1 := (by with_unfolding_all exact (A.chr.e1 :)))
      (unr_iff := (by with_unfolding_all exact (A.chr.unr_iff :)))
      (frob := (by with_unfolding_all exact (A.chr.frob :)))
      (tw := (by with_unfolding_all exact (A.chr.tw :)))
      (infG := (by with_unfolding_all exact (A.chr.infG :)))
      (csd := (by with_unfolding_all exact (A.chr.csd :)))
      (etaT := (by with_unfolding_all exact (A.chr.etaT :)))
      (etaTinv := (by with_unfolding_all exact (A.chr.etaTinv :)))
      (plGw := (by with_unfolding_all exact (A.chr.plGw :))))
    (row := @_root_.GlobalTheory.HeightCounting.RowSide.mk (_)
      (locR := (by with_unfolding_all exact (A.row.locR :)))
      (satR := (by with_unfolding_all exact (A.row.satR :)))
      (lab_eq := (by with_unfolding_all exact (A.row.lab_eq :))))
    (pl := @_root_.GlobalTheory.HeightCounting.PlSide.mk (_)
      (ι := (by with_unfolding_all exact (A.pl.ι :)))
      (ι_w := (by with_unfolding_all exact (A.pl.ι_w :)))
      (plB := (by with_unfolding_all exact (A.pl.plB :)))
      (plB_eq := (by with_unfolding_all exact (A.pl.plB_eq :)))
      (plκ := (by with_unfolding_all exact (A.pl.plκ :))))
    (iota := (by with_unfolding_all exact (A.iota :)))
    (wd := @_root_.GlobalTheory.HeightCounting.WDSide.mk (_) (_)
      (wdOf := (by with_unfolding_all exact (A.wd.wdOf :)))
      (wdOf_dim := (by with_unfolding_all exact (A.wd.wdOf_dim :)))
      (wdOf_unr := (by with_unfolding_all exact (A.wd.wdOf_unr :)))
      (wdOf_frob := (by with_unfolding_all exact (A.wd.wdOf_frob :)))
      (wdOf_ine := (by with_unfolding_all exact (A.wd.wdOf_ine :)))
      (wdOf_mono0 := (by with_unfolding_all exact (A.wd.wdOf_mono0 :)))
      (IsCrysW := (by with_unfolding_all exact (A.wd.IsCrysW :)))
      (IsPotCrysW := (by with_unfolding_all exact (A.wd.IsPotCrysW :)))
      (IsdRW := (by with_unfolding_all exact (A.wd.IsdRW :)))
      (jumpsW := (by with_unfolding_all exact (A.wd.jumpsW :)))
      (wdOf_unrL := (by with_unfolding_all exact (A.wd.wdOf_unrL :)))
      (wdOf_mono0L := (by with_unfolding_all exact (A.wd.wdOf_mono0L :)))
      (away := (by with_unfolding_all exact (A.wd.away :)))
      (above := (by with_unfolding_all exact (A.wd.above :)))
      (loc := (by with_unfolding_all exact (A.wd.loc :))))
    (grp := @_root_.GlobalTheory.HeightCounting.GrpSide.mk (_)
      (tA := (by with_unfolding_all exact (A.grp.tA :)))
      (tκ := (by with_unfolding_all exact (A.grp.tκ :)))
      (teichC_def := (by with_unfolding_all exact (A.grp.teichC_def :)))
      (ζ := (by with_unfolding_all exact (A.grp.ζ :)))
      (ζ_gen := (by with_unfolding_all exact (A.grp.ζ_gen :)))
      (O := (by with_unfolding_all exact (A.grp.O :)))
      (eSer_def := (by with_unfolding_all exact (A.grp.eSer_def :)))
      (kv := (by with_unfolding_all exact (A.grp.kv :)))
      (tg_tame := (by with_unfolding_all exact (A.grp.tg_tame :)))
      (O_equiv := (by with_unfolding_all exact (A.grp.O_equiv :)))
      (O_tw := (by with_unfolding_all exact (A.grp.O_tw :))))
    (par := @_root_.GlobalTheory.HeightCounting.ParSide.mk (_) (_)
      (eM := (by with_unfolding_all exact (A.par.eM :)))
      (eM_K := (by with_unfolding_all exact (A.par.eM_K :)))
      (eP := (by with_unfolding_all exact (A.par.eP :)))
      (locPar_def := (by with_unfolding_all exact (A.par.locPar_def :))))
    (au := @_root_.GlobalTheory.HeightCounting.AUSideAlt.mk (_)
      (cls := (by with_unfolding_all exact (A.au.cls :)))
      (surj := (by with_unfolding_all exact (A.au.surj :)))
      (iso := (by with_unfolding_all exact (A.au.iso :)))
      (mult := (by with_unfolding_all exact (A.au.mult :)))
      (sph := (by with_unfolding_all exact (A.au.sph :)))
      (sat := (by with_unfolding_all exact (A.au.sat :)))
      (clsWt := (by with_unfolding_all exact (A.au.clsWt :)))
      (surjWt := (by with_unfolding_all exact (A.au.surjWt :)))
      (isoWt := (by with_unfolding_all exact (A.au.isoWt :)))
      (wt := (by with_unfolding_all exact (A.au.wt :)))
      (infW := (by with_unfolding_all exact (A.au.infW :)))
      (locUnr := (by with_unfolding_all exact (A.au.locUnr :)))
      (locPol := (by with_unfolding_all exact (A.au.locPol :))))
    (chiT := (by with_unfolding_all exact (A.chiT :)))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideB
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def Mv.sideB_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {low Pq S hk eig θ} (x : SideB D cf A.row low Pq S hk eig θ) : SideB m.D (m.cf cf) (m.sideA_alt A).row low Pq S hk eig θ := @_root_.GlobalTheory.HeightCounting.SideB.mk (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (twF := @_root_.GlobalTheory.HeightCounting.TwFrameC.mk (_)
      (K0 := (by with_unfolding_all exact (x.twF.K0 :)))
      (eO0 := (by with_unfolding_all exact (x.twF.eO0 :)))
      (j0 := (by with_unfolding_all exact (x.twF.j0 :)))
      (Lw := (by with_unfolding_all exact (x.twF.Lw :)))
      (eO := (by with_unfolding_all exact (x.twF.eO :)))
      (eOk := (by with_unfolding_all exact (x.twF.eOk :)))
      (iCq := (by with_unfolding_all exact (x.twF.iCq :)))
      (S0x := (by with_unfolding_all exact (x.twF.S0x :))))
    (tw := @_root_.GlobalTheory.HeightCounting.TwistFrameLowIndexCompatibility.mk (_) (_) (_)
      (pl_emb := (by with_unfolding_all exact (x.tw.pl_emb :)))
      (ringSpec_baseIntegersEquiv_algebraMap := (by with_unfolding_all exact (x.tw.ringSpec_baseIntegersEquiv_algebraMap :)))
      (ringSpec_baseEmbedding_compatible := (by with_unfolding_all exact (x.tw.ringSpec_baseEmbedding_compatible :)))
      (eO_alg := (by with_unfolding_all exact (x.tw.eO_alg :)))
      (eOk_alg := (by with_unfolding_all exact (x.tw.eOk_alg :)))
      (mu_g := (by with_unfolding_all exact (x.tw.mu_g :)))
      (hk_split := (by with_unfolding_all exact (x.tw.hk_split :)))
      (ringSpec_excludedPlaces_eq := (by with_unfolding_all exact (x.tw.ringSpec_excludedPlaces_eq :)))
      (concreteTwistFrame_extraExcludedPlaces_conj := (by with_unfolding_all exact (x.tw.concreteTwistFrame_extraExcludedPlaces_conj :)))
      (B_range := (by with_unfolding_all exact (x.tw.B_range :)))
      (sig_inj := (by with_unfolding_all exact (x.tw.sig_inj :)))
      (qs_pos := (by with_unfolding_all exact (x.tw.qs_pos :)))
      (concreteTwistFrame_extraExcluded_over_smallPrimes := (by with_unfolding_all exact (x.tw.concreteTwistFrame_extraExcluded_over_smallPrimes :))))
    (cover := (by with_unfolding_all exact (x.cover :)))
    (chiD := @_root_.Formalism.L2.NC.NChiData.mk (_)
      (mu0 := (by with_unfolding_all exact (x.chiD.mu0 :)))
      (etaT := (by with_unfolding_all exact (x.chiD.etaT :)))
      (del := (by with_unfolding_all exact (x.chiD.del :)))
      (psi := (by with_unfolding_all exact (x.chiD.psi :)))
      (chiI := (by with_unfolding_all exact (x.chiD.chiI :)))
      (embO := (by with_unfolding_all exact (x.chiD.embO :))))
    (chi := @_root_.Formalism.L2.NC.NormalizedCharacterCompatibility.mk (_) (_)
      (psi := (by with_unfolding_all exact (x.chi.psi :)))
      (del_fix := (by with_unfolding_all exact (x.chi.del_fix :)))
      (delta := (by with_unfolding_all exact (x.chi.delta :)))
      (chi1 := (by with_unfolding_all exact (x.chi.chi1 :)))
      (ringSpec_sidedEmbedding_fixedField := (by with_unfolding_all exact (x.chi.ringSpec_sidedEmbedding_fixedField :)))
      (etaT_unr := (by with_unfolding_all exact (x.chi.etaT_unr :)))
      (etaT_inf := (by with_unfolding_all exact (x.chi.etaT_inf :)))
      (lamG := (by with_unfolding_all exact (x.chi.lamG :))))
    (eta_eq := (by with_unfolding_all exact (x.eta_eq :)))
    (ringSpec_normalisedCharacter_eq := (by with_unfolding_all exact (x.ringSpec_normalisedCharacter_eq :)))
    (del_eq := (by with_unfolding_all exact (x.del_eq :)))
    (iCq_embO := (by with_unfolding_all exact (x.iCq_embO :)))
    (embO_star := (by with_unfolding_all exact (x.embO_star :)))
    (deltaRead := (by with_unfolding_all exact (x.deltaRead :)))
    (exp := @_root_.Formalism.L2.NExpTied.mk (_)
      (U_eq := (by with_unfolding_all exact (x.exp.U_eq :)))
      (psiU_gen := (by with_unfolding_all exact (x.exp.psiU_gen :)))
      (psiU_side := (by with_unfolding_all exact (x.exp.psiU_side :)))
      (psiU_xi := (by with_unfolding_all exact (x.exp.psiU_xi :)))
      (delU_cont := (by with_unfolding_all exact (x.exp.delU_cont :)))
      (delU_ine := (by with_unfolding_all exact (x.exp.delU_ine :)))
      (thU_empty := (by with_unfolding_all exact (x.exp.thU_empty :)))
      (sgnT := (by with_unfolding_all exact (x.exp.sgnT :)))
      (sgnT_one := (by with_unfolding_all exact (x.exp.sgnT_one :)))
      (Wt := (by with_unfolding_all exact (x.exp.Wt :)))
      (acgWt := (by with_unfolding_all exact (x.exp.acgWt :)))
      (modWt := (by with_unfolding_all exact (x.exp.modWt :)))
      (fdWt := (by with_unfolding_all exact (x.exp.fdWt :)))
      (rhoW := (by with_unfolding_all exact (x.exp.rhoW :)))
      (rhoW_irr := (by with_unfolding_all exact (x.exp.rhoW_irr :)))
      (rhoW_alg := (by with_unfolding_all exact (x.exp.rhoW_alg :)))
      (tauG := (by with_unfolding_all exact (x.exp.tauG :)))
      (sgnG := (by with_unfolding_all exact (x.exp.sgnG :)))
      (sgnG_one := (by with_unfolding_all exact (x.exp.sgnG_one :)))
      (tau_galois_first_character := (by with_unfolding_all exact (x.exp.tau_galois_first_character :)))
      (mtV := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => @fun x6 => @fun x7 => @fun x8 => @fun x9 => @_root_.Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).W : _)))
        (acg := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).acg : _)))
        (mod := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).mod : _)))
        (fd := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).fd : _)))
        (ρ := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).ρ : _)))
        (irr := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).irr : _)))
        (alg := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).alg : _)))
        (bc := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).bc : _)))
        (J := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J : _)))
        (χ := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).χ : _)))
        (J_open := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_open : _)))
        (hyp := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).hyp : _)))
        (QP := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP : _)))
        (QP_sub := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_sub : _)))
        (QP_cover := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_cover : _)))
        (QP_nconj := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_nconj : _)))
        (DP := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP : _)))
        (DP_sub := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_sub : _)))
        (DP_cover := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_cover : _)))
        (DP_nconj := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_nconj : _)))
        (sp := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp : _)))
        (sp_w := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp_w : _)))
        (redG := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).redG : _)))
        (J_mem := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_mem : _)))
        (chi_eq := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).chi_eq : _)))
        (real := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).real : _))))
      (rhoW_hw := (by with_unfolding_all exact (x.exp.rhoW_hw :)))
      (rhoW_wt := (by with_unfolding_all exact (x.exp.rhoW_wt :))))
    (pq := (by with_unfolding_all exact (x.pq :)))
    (psiU := (by with_unfolding_all exact (x.psiU :)))
    (rho := (by with_unfolding_all exact (x.rho :)))
    (chiL := (by with_unfolding_all exact (x.chiL :)))
    (hs := (by with_unfolding_all exact (x.hs :)))
    (eF := (by with_unfolding_all exact (x.eF :)))
    (bsup := (by with_unfolding_all exact (x.bsup :)))
    (act := (by with_unfolding_all exact (x.act :)))
    (cHk := (by with_unfolding_all exact (x.cHk :)))
    (hkEq := (by with_unfolding_all exact (x.hkEq :)))
    (cHk_del := (by with_unfolding_all exact (x.cHk_del :)))
    (hk_emb := (by with_unfolding_all exact (x.hk_emb :)))
    (sigSpan := (by with_unfolding_all exact (x.sigSpan :)))
    (rowS := (by with_unfolding_all exact (x.rowS :)))
    (rowS_eig := (by with_unfolding_all exact (x.rowS_eig :)))
    (hEig_zero := (by with_unfolding_all exact (x.hEig_zero :)))
    (rhoS := (by with_unfolding_all exact (x.rhoS :)))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpec
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.ndSpec_alt {big} {L : LocAll (lay0 D)} (x : NdSpec A.pl M C big L.X L.T) : NdSpec (m.sideA_alt A).pl (m.mt M) (m.ch C) big (m.loc L).X (m.loc L).T := @_root_.GlobalTheory.HeightCounting.NdSpec.mk (_) (_) (_) (_) (_) (_) (_)
    (iq := (by with_unfolding_all exact (x.iq :)))
    (iq_alg := (by with_unfolding_all exact (x.iq_alg :)))
    (iq_LL := (by with_unfolding_all exact (x.iq_LL :)))
    (iq_big := (by with_unfolding_all exact (x.iq_big :)))
    (B := @_root_.Formalism.L2.NLocBase.mk (_) (_)
      (Oc := (by with_unfolding_all exact (x.B.Oc :)))
      (ringOc := (by with_unfolding_all exact (x.B.ringOc :)))
      (domOc := (by with_unfolding_all exact (x.B.domOc :)))
      (dvrOc := (by with_unfolding_all exact (x.B.dvrOc :)))
      (ec := (by with_unfolding_all exact (x.B.ec :)))
      (ec_w := (by with_unfolding_all exact (x.B.ec_w :)))
      (V := (by with_unfolding_all exact (x.B.V :)))
      (acgV := (by with_unfolding_all exact (x.B.acgV :)))
      (modV := (by with_unfolding_all exact (x.B.modV :)))
      (modVO := (by with_unfolding_all exact (x.B.modVO :)))
      (towV := (by with_unfolding_all exact (x.B.towV :)))
      (iV := (by with_unfolding_all exact (x.B.iV :)))
      (iV_basis := (by with_unfolding_all exact (x.B.iV_basis :)))
      (Qc := (by with_unfolding_all exact (x.B.Qc :)))
      (hL := (by with_unfolding_all exact (x.B.hL :)))
      (hL_def := (by with_unfolding_all exact (x.B.hL_def :)))
      (hK := (by with_unfolding_all exact (x.B.hK :)))
      (hK_def := (by with_unfolding_all exact (x.B.hK_def :)))
      (split := (by with_unfolding_all exact (x.B.split :)))
      (Qc_over := (by with_unfolding_all exact (x.B.Qc_over :)))
      (Qc_conj := (by with_unfolding_all exact (x.B.Qc_conj :))))
    (Q_eq := (by with_unfolding_all exact (x.Q_eq :)))
    (mx := (by with_unfolding_all exact (x.mx :)))
    (mx_max := (by with_unfolding_all exact (x.mx_max :)))
    (mx_inj := (by with_unfolding_all exact (x.mx_inj :)))
    (mx_all := (by with_unfolding_all exact (x.mx_all :)))
    (phO := (by with_unfolding_all exact (x.phO :)))
    (phK := (by with_unfolding_all exact (x.phK :)))
    (phK_alg := (by with_unfolding_all exact (x.phK_alg :)))
    (phK_emb := (by with_unfolding_all exact (x.phK_emb :)))
    (Psi := (by with_unfolding_all exact (x.Psi :)))
    (Psi_inj := (by with_unfolding_all exact (x.Psi_inj :)))
    (Psi_range := (by with_unfolding_all exact (x.Psi_range :)))
    (Psi_pr := (by with_unfolding_all exact (x.Psi_pr :)))
    (ptX := (by with_unfolding_all exact (x.ptX :)))
    (ptX_hT := (by with_unfolding_all exact (x.ptX_hT :)))
    (iotaC := (by with_unfolding_all exact (x.iotaC :)))
    (iotaC_coh := (by with_unfolding_all exact (x.iotaC_coh :)))
    (Qc_eq := (by with_unfolding_all exact (x.Qc_eq :)))
    (std := (by with_unfolding_all exact (x.std :)))
    (act_hK := (by with_unfolding_all exact (x.act_hK :)))
    (twOf_eq := (by with_unfolding_all exact (x.twOf_eq :)))
    (twSide_eq := (by with_unfolding_all exact (x.twSide_eq :)))
    (psi_eq := (by with_unfolding_all exact (x.psi_eq :)))
    (twO_alg := (by with_unfolding_all exact (x.twO_alg :)))
    (tw_reads := (by with_unfolding_all exact (x.tw_reads :)))
    (heckeLoc_gamma_places := (by with_unfolding_all exact (x.heckeLoc_gamma_places :)))
    (nbr := (by with_unfolding_all exact (x.nbr :)))
    (nbr_ind := (by with_unfolding_all exact (x.nbr_ind :)))
    (self_good := (by with_unfolding_all exact (x.self_good :)))
    (nbr_iq := (by with_unfolding_all exact (x.nbr_iq :)))
    (bj := (by with_unfolding_all exact (x.bj :)))
    (bj_span := (by with_unfolding_all exact (x.bj_span :)))
    (bj_rel := (by with_unfolding_all exact (x.bj_rel :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvCg
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000
def mvCg_alt (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE}
    (x : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT) : _root_.GlobalTheory.HeightCounting.CGTrueT hL m.D (m.sideA_alt A).wdT :=
  @_root_.UpperTheory.One.M.New.cgMk _ _ _ s ((by with_unfolding_all exact (x.e :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgGood s x) :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgSurj x) :))) ((by with_unfolding_all exact (x.zero :))) ((by with_unfolding_all exact (x.loc :))) ((by with_unfolding_all exact (x.tw :))) ((by with_unfolding_all exact (x.inf :))) ((by with_unfolding_all exact (x.csd :)))
end UpperTheory.One.M
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChoiceSide
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.choiceSide_alt {low Pq S hk eig θ} {Bs : SideB D cf A.row low Pq S hk eig θ} (x : ChoiceSide D cf M Bs.exp C tp) : ChoiceSide m.D (m.cf cf) (m.mt M) (m.sideB_alt Bs).exp (m.ch C) (m.tp tp) := @_root_.GlobalTheory.HeightCounting.ChoiceSide.mk (_) (_) (_) (_) (_) (_)
    (nct := @_root_.Formalism.BasicNotions.NChTie.mk (_) (_)
      (twOf_eq := (by with_unfolding_all exact (x.nct.twOf_eq :)))
      (twSide_eq := (by with_unfolding_all exact (x.nct.twSide_eq :)))
      (Q_eq := (by with_unfolding_all exact (x.nct.Q_eq :)))
      (psi_eq := (by with_unfolding_all exact (x.nct.psi_eq :)))
      (embedding_baseField_condition := (by with_unfolding_all exact (x.nct.embedding_baseField_condition :))))
    (choice := @_root_.GlobalTheory.HeightCounting.ChoiceC.mk (_) (_)
      (twI_conj := (by with_unfolding_all exact (x.choice.twI_conj :)))
      (sd_place := (by with_unfolding_all exact (x.choice.sd_place :)))
      (emb_side := (by with_unfolding_all exact (x.choice.emb_side :)))
      (sd_conj := (by with_unfolding_all exact (x.choice.sd_conj :)))
      (one := (by with_unfolding_all exact (x.choice.one :)))
      (conj := (by with_unfolding_all exact (x.choice.conj :))))
    (off := (by with_unfolding_all exact (x.off :)))
    (adm := (by with_unfolding_all exact (x.adm :)))
    (psi := (by with_unfolding_all exact (x.psi :)))
    (eMt_level := (by with_unfolding_all exact (x.eMt_level :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutSpec
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.autSpec_alt {big} {L : LocAll (lay0 D)} {Sp : NdSpec A.pl M C big L.X L.T} (x : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation (m.sideA_alt A) (m.mt M) (m.tp tp).tup (m.ndSpec_alt Sp).iq (m.loc L).Y (m.loc L).C := @_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (iotaQ := (by with_unfolding_all exact (x.iotaQ :)))
    (iotaQC := (by with_unfolding_all exact (x.iotaQC :)))
    (kFbar := (by with_unfolding_all exact (x.kFbar :)))
    (locW := (by with_unfolding_all exact (x.locW :)))
    (satW := (by with_unfolding_all exact (x.satW :)))
    (wdOf := (by with_unfolding_all exact (x.wdOf :)))
    (muC := (by with_unfolding_all exact (x.muC :)))
    (S := (by with_unfolding_all exact (x.S :)))
    (irr := (by with_unfolding_all exact (x.irr :)))
    (inj := (by with_unfolding_all exact (x.inj :)))
    (surj := (by with_unfolding_all exact (x.surj :)))
    (typeV := (by with_unfolding_all exact (x.typeV :)))
    (ptV := (by with_unfolding_all exact (x.ptV :)))
    (emb := (by with_unfolding_all exact (x.emb :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhtOn
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.phtOn_alt {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {fr : Formalism.L2.OmFrame D} (x : PhtOn A.wd fr fun _ _ _ _ => True) : PhtOn (m.sideA_alt A).wd (m.omFrame fr) fun _ _ _ _ => True := @_root_.GlobalTheory.HeightCounting.PhtOn.mk (_) (_) (_) (_) (_)
    (card := (by with_unfolding_all exact (x.card :)))
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphyOfMove
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem Mv.automorphy_of_move {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} (x : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au) : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL m.D (m.sideA_alt A).wdT (m.sideA_alt A).au := (by with_unfolding_all exact (x :))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabConj
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.labConj_alt (x : LabConj D A.wdT) : LabConj m.D (m.sideA_alt A).wdT := (by with_unfolding_all exact (x :))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrimitiveAtLinkedAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem Mv.herm_wCell_last_mul_mulVec_eq_of_inWb {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {rep} (x : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w ↦ (A.wdT.e w) (A.row.locR σ w)) A.row.satR) : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL m.D rep (fun σ w ↦ ((m.sideA_alt A).wdT.e w) ((m.sideA_alt A).row.locR σ w)) (m.sideA_alt A).row.satR := (by with_unfolding_all exact (x :))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
end
theorem Mv.exists_at_alt {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) :
    ∃ a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL m.D (m.cf cf) (m.ch C) (m.tp tp), _root_.GlobalTheory.LayerMove.AtSameAltAlt m a a' := by
  obtain ⟨⟨nb, pack⟩, all, chr_eq, host, frameN, chrN, chrGal, Pq', Pq_over, pq, jE_eq, mt_eq, Pq_eq, hlow, split, ratIn,
    r1, r2, r3, depth⟩ := a
  obtain ⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, eq⟩ := nb
  subst eq
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at pack
  obtain ⟨rfl, rfl, rfl⟩ := pack
  have hmt : mtL L M = all.gal.mt := eq_of_heq mt_eq
  refine ⟨@_root_.GlobalTheory.Mem.Top.Bl.NAtData.mk hL m.D _ _ _
    (⟨@_root_.GlobalTheory.HeightCounting.NormChoiceConstructed.mk hL m.D m.pre.D (m.pre.cf cf0) jE (m.pre.sideA_alt A) ((_root_.UpperTheory.One.M.mvCg_alt trivial) m.pre cg) (m.pre.automorphy_of_move au) rep (m.pre.herm_wCell_last_mul_mulVec_eq_of_inWb row) low Pq S hk eig θ
      (m.pre.sideB_alt Bs) (m.pre.mt M) (m.pre.ch C0) (m.pre.tp tp0) (m.pre.choiceSide_alt ch) (m.pre.mtInput mt) big (m.pre.loc L)
      (m.pre.ndSpec_alt Sp) (m.pre.autSpec_alt Au) ((by with_unfolding_all exact (ss :))) m.withLoc_pre, m.pack_pre tp0⟩)
    ((_root_.UpperTheory.One.M.mvAll_alt trivial) m all)
    ((by with_unfolding_all exact ((congrArg (fun p : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L C0) =>
      (⟨m.cf p.1, m.tp p.2⟩ : Σ c : CharFrame m.D, TupTied m.D c (m.ch (chL L C0)))) chr_eq) :)))
    (m.host host) ((by with_unfolding_all exact (frameN :))) (m.chrN chrN) (m.chrGal chrGal) ((by with_unfolding_all exact (Pq' :))) ((by with_unfolding_all exact (Pq_over :))) ((by with_unfolding_all exact (pq :))) ((by with_unfolding_all exact (jE_eq :)))
    ((by with_unfolding_all exact ((heq_of_eq (congrArg m.mt hmt)) :))) ((by with_unfolding_all exact (Pq_eq :))) ((by with_unfolding_all exact (hlow :))) (m.oSplit split) ((by with_unfolding_all exact ((m.pre.ratIn ratIn) :))) ((by with_unfolding_all exact (r1 :))) ((by with_unfolding_all exact (r2 :)))
    ((by with_unfolding_all exact (r3 :))) ((by with_unfolding_all exact ((m.pre.rowDepth depth) :))), ?_⟩
  refine ⟨HEq.rfl, (by with_unfolding_all exact ((HEq.refl Pq') :)), (by with_unfolding_all exact ((HEq.refl (ratL L S)) :)), (by with_unfolding_all exact ((HEq.refl hk) :)), (by with_unfolding_all exact ((HEq.refl rep) :)), (by with_unfolding_all exact ((HEq.refl eig) :)), ?_⟩
  rintro ⟨h1, h2, fr, h3, h4⟩
  exact ⟨(by with_unfolding_all exact ((m.pre.labConj_alt (A := A) h1) :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact ((m.pre.omFrame fr) :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact ((m.pre.phtOn_alt (A := A) h4) :))⟩
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsSameGeometricHalf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.SerCopy
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.LayerMove.SerUp
variable {B : GlobalTheory.Mem.Base} {C : Cols B} {W : RowsRest B C} (o : Oth W) (V' : DivStage B C W) (S' : SStage B C W)
variable {o} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 o.L.D.what₂.LL G Pl0 I0 (List ℕ) T o.L.D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks o.L.D.what₂.LL] {R : RealDat3 o.L.D A3 Ks}
  {cG : G0 R.Pg o.L.D.R.r ≃* G0g o.L.D.nd} {S : RatDat o.L.D.ntw} {YS : NExpRealS R cG S}
  {v₀ : ∀ (j : Fin o.L.D.R.m) (σ : o.L.D.what₂.LL →+* ℂ), (R.MW j σ).Vec}
end GlobalTheory.LayerMove.SerUp
end
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
open GlobalTheory.LayerMove
set_option maxHeartbeats 1000000
theorem _root_.GlobalTheory.T.geo_heq_geoHalf_of_same : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → HEq t'.r.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : _root_.GlobalTheory.HeightCounting.NAllCAlt (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq') := by
  intro K B f T w Z Wt S' N h nch p0 t p0' t' hs hg
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  have e7 : geo' = (by with_unfolding_all exact ((GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) :)) := eq_of_heq ((by with_unfolding_all exact (hg :)))
  subst e7
  intro kKs hk YS kKs' hk' YS' hkk hfi heF a X' hX PV PV' hPV Pq Pq' hPq s
  have e8 : kKs' = (by with_unfolding_all exact (kKs :)) := eq_of_heq ((by with_unfolding_all exact (hkk :)))
  subst e8
  obtain ⟨fi', geq', rho', chi', eF', bsup', act'⟩ := YS'
  have e9 : fi' = (by with_unfolding_all exact (YS.fi :)) := eq_of_heq ((by with_unfolding_all exact (hfi :)))
  have e10 : eF' = (by with_unfolding_all exact (YS.eF :)) := eq_of_heq ((by with_unfolding_all exact (heF :)))
  subst e9 e10
  have e11 : X' = (by with_unfolding_all exact (((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp :)) := eq_of_heq ((by with_unfolding_all exact (hX :)))
  have e12 : Pq' = (by with_unfolding_all exact (Pq :)) := eq_of_heq ((by with_unfolding_all exact (hPq :)))
  subst e11 e12
  have e13 : (fun i => (PV' i).ψ) = (by with_unfolding_all exact ((fun i => (PV i).ψ) :)) := eq_of_heq ((by with_unfolding_all exact (hPV :)))
  have e14 : PV' = fun j => @Formalism.IndefR.principalLevelFrame.RowPsi.mk _ _ _ ((by with_unfolding_all exact ((PV ((j))).ψ : _))) ((by with_unfolding_all exact ((PV ((j))).inj : _))) ((by with_unfolding_all exact ((PV ((j))).into : _)))
      ((by with_unfolding_all exact ((PV ((j))).onto : _))) := funext fun j => SerUp.rowPsi_ext ((by with_unfolding_all exact ((congrFun e13 j) :)))
  subst e14
  exact ⟨@SerAt.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (ex := (by with_unfolding_all exact ((@SerUp.ex B w.C Z.W ⟨Z.V, Z.S, Z.N, Z.G⟩ (upL Z S' N h).V S' _ _ _ _ _ _ _ _ _ _ t.r.z.alg t.r.z.R t.r.z.cG _ YS
      t.r.z.geo.v₀ s.ex) :)))
    (bad := (by with_unfolding_all exact (s.bad :))) (ch := (by with_unfolding_all exact (s.ch :))) (join := (by with_unfolding_all exact (s.join :))) (sup := (by with_unfolding_all exact (s.sup :))) (off := (by with_unfolding_all exact (s.off :)))
    (lam := (by with_unfolding_all exact (((mvOf w Z S' N h).lam s.lam) :)))
    (lam_ok := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_ok s.lam_ok) :)))
    (lam_teich := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_teich s.lam_teich) :)))
    (lam_C := (by with_unfolding_all exact ((congrArg (mvOf w Z S' N h).cf s.lam_C) :)))
    (lam_q := (by with_unfolding_all exact (s.lam_q :)))
    (lam_tie := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_tie s.lam_tie) :)))⟩
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUp
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}
end
theorem exists_kept_nChoice_thData_upL : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z)), ∃ (nch' : NChoice (w.D (upL Z S' N h))) (xd' : ThData (w.D (upL Z S' N h))), Kept nch nch' ∧ (S' = Z.S → HEq nch' (nchTr (D := w.D Z) N h nch) ∧ HEq xd' (xdTr (D := w.D Z) N h xd)) ∧ (NchT w Z Wt nch → Nonempty (NchT w (upL Z S' N h) Wt nch')) ∧ (GoodO (w.D Z) nch xd → GoodO (w.D (upL Z S' N h)) nch' xd') ∧ ∀ (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (n : NchT w Z Wt nch) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0') (n' : NchT w (upL Z S' N h) Wt nch'), RowsSame t t' → HEq t'.r.z.geo (_root_.GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) K B f T w Z Wt p0 t nch n xd → Nonempty (_root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) K B f T w (upL Z S' N h) Wt p0' t' nch' n' xd') := by
  intro hL K B f T w Z Wt S' N h nch xd
  refine ⟨nchUp S' N h nch, xdUp S' N h xd, kept_up S' N h nch, ?_, nchT_up S' N h, goodO_up S' N h, ?_⟩
  · rintro rfl
    exact ⟨HEq.rfl, HEq.rfl⟩
  · rintro p0 t n p0' t' ⟨tp', xi', psi', tie', Q', chr'⟩ hs hg ⟨c, e, ⟨bk⟩⟩
    have e1 : tp' = (by with_unfolding_all exact (((mvOf w Z S' N h).tp n.tp) :)) := tupTied_ext (xi'.trans ((by with_unfolding_all exact (n.xi.symm :)))) (psi'.trans ((by with_unfolding_all exact (n.psi.symm :))))
    subst e1
    obtain ⟨a', hA⟩ := (mvOf w Z S' N h).exists_at_alt c.a
    obtain ⟨r', ⟨e'⟩⟩ := exists_nonempty_nMore_upL hL K B f T w Z Wt S' N h nch xd
      p0 t p0' t' hs hg
      (_root_.GlobalTheory.T.rowReadings_sameRows_identify_definiteForms K B f T w Z Wt S' N h p0 t p0' t' hs)
      (_root_.GlobalTheory.T.geo_heq_geoHalf_of_same K B f T w Z Wt S' N h nch p0 t p0' t' hs hg)
      (tp' := by with_unfolding_all exact (mvOf w Z S' N h).tp n.tp)
      c.a (by with_unfolding_all exact a') (by with_unfolding_all exact hA) c.row e
    have hq : a'.Pq = (by with_unfolding_all exact (c.a.Pq :)) := eq_of_heq ((by with_unfolding_all exact (hA.2.1 :)))
    have hsel : Set.range a'.Pq = (by with_unfolding_all exact ((Set.range w.I.sel) :)) := (congrArg Set.range hq).trans ((by with_unfolding_all exact (c.sel :)))
    exact ⟨⟨⟨(by with_unfolding_all exact (a' :)), (by with_unfolding_all exact (r' :)), (by with_unfolding_all exact (hsel :))⟩, (by with_unfolding_all exact (e' :)), ⟨(by with_unfolding_all exact (((mvOf w Z S' N h).bkLaw bk) :))⟩⟩⟩
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUpStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z)), ∃ (nch' : NChoice (w.D (upL Z S' N h))) (xd' : ThData (w.D (upL Z S' N h))), Kept nch nch' ∧ (S' = Z.S → HEq nch' (nchTr (D := w.D Z) N h nch) ∧ HEq xd' (xdTr (D := w.D Z) N h xd)) ∧ (NchT w Z Wt nch → Nonempty (NchT w (upL Z S' N h) Wt nch')) ∧ (GoodO (w.D Z) nch xd → GoodO (w.D (upL Z S' N h)) nch' xd') ∧ ∀ (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (n : NchT w Z Wt nch) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0') (n' : NchT w (upL Z S' N h) Wt nch'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) K B f T w Z Wt p0 t nch n xd → Nonempty (_root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) K B f T w (upL Z S' N h) Wt p0' t' nch' n' xd') := by
  exact _root_.GlobalTheory.LayerMove.exists_kept_nChoice_thData_upL
end
end
