module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingDefiniteBaseVanishOfMiStar2
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Div

theorem pairing_definite_base_vanish_of_miStar2 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), (R.toCx3 F).MIstar2 (F.eV (R.toCx3 F).zs) sEE → CxData.BtVanish (fc := F.fc) (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hsep hC hP sEE hM
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP
  obtain ⟨d, hU, hI, -⟩ := hM
  exact CxData.base_tuple_vanishing_of_hypotheses _ F.cr F.cv hR.jIsoR (hR.levs true).1 (hR.levs true).2.1 (hR.levs true).2.2
    (definite_coordinates_in_good_part _ true) (EvTie.evTie_of_ok hOk F _) hU hI

end GlobalTheory.Div
end

noncomputable section

namespace GlobalTheory.Fc.DivLinked

section Read

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}


set_option maxHeartbeats 2000000 in
theorem divisionRows_pairing_vanishes_of_rational_pairing_law
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay) (x : GlobalTheory.Mem.R3.TwIn ex) (hH : Holds x.R x.F) (hB : Rw.BkLaw D)
    (hV : CxData.BtVanish (fc := x.F.fc) (x.R.toCx3 x.F)) : GlobalTheory.Cp.DivRows3G (GlobalTheory.Mem.R3.divisionPairOfAdelicFormsFaceColumnsData x) := by
  have hRational := GlobalTheory.T.divisionPairing_rational_on_rationalPoints'
    hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.pins hH
  have hRows := (GlobalTheory.T.divisionCompatible_at_readIdentifications
    hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.sEE Yd x.JM x.pins hH
    (fun _ _ => x.div.grp)).2 x.mjH ex.idx (hB hRational) hV
  exact {
    sharpRR := hRows.sharpRR
    baseRR := hRows.baseRR
    divisionRows_rationalLift := fun i t _ => hRows.divisionRows_rationalLift i t
    thTheta := fun i t _ v => hRows.thTheta i t v
    num := ⟨fun i t _ w => hRows.num.Ij i t w, fun i t _ w => hRows.num.jw i t w, hRows.num.etaJ⟩
    colsBk := hRows.colsBk }

end Read

end GlobalTheory.Fc.DivLinked

end
