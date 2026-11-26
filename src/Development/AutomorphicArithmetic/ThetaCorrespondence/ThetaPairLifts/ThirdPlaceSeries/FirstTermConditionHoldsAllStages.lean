module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglands

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GoodFirst
set_option maxHeartbeats 2000000 in
theorem firstTermCondition_forall_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GoodFTAll (Dof x) := by
  intro hP hL
  have h := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (_root_.GlobalTheory.T.nonGalois_typeVec_fixed_by_e0 hP)
  refine EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp fo tr w s P x l => ?_
  have hloc := H kp fo tr w s P x
  have ty : TypesTrue (Dof x).ntypes (Fr.at (w.st x.o.Z) f).P (Fr.at (w.st x.o.Z) f).W := x.fits.grp
  exact _root_.UpperTheory.Lit.Dz.firstTermCondition_all_stages hP.green hP.zel hL (Dof x) (cfOf x) (repOf x.r.Y) l.a
    (GlobalTheory.CoefDuty.OPinModel.labFixed_of_typesTrue ty) hloc
end GlobalTheory.GoodFirst
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allSt_goodFTAll_of_levelA : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GoodFTAll (Dof x) := by
  first | exact @_root_.GlobalTheory.GoodFirst.firstTermCondition_forall_stages_alt | exact _root_.GlobalTheory.GoodFirst.firstTermCondition_forall_stages_alt | (intros; apply _root_.GlobalTheory.GoodFirst.firstTermCondition_forall_stages_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemSatisfiesLocalProperty
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabFixedIff
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CoefDuty.OPinModel
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.Mem.Col2
theorem labFixed_iff_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : LabFixed D ↔ LabFixed a.nt.D := by
  have e : ∀ D', D' = withLoc a.nt.L → (LabFixed D' ↔ LabFixed a.nt.D) := by
    rintro _ rfl
    exact labFixed_withLoc _
  exact e D a.nt.eq
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
theorem labDat_gen_tame_at_plGw {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} (h : _root_.GlobalTheory.CoefDuty.OPinAlt a) (k : Fin 2) (v : a.nt.D.nd.PlG k) :
    @Formalism.L2.NT.TameCoupled _ _ _ _ _ (a.nt.D.nd.plOm.1 (a.nt.D.naut.plGw k v)) _ ⟨a.nt.D.host.g_prime k⟩ (a.nt.A.grp.kv k v)
      (a.nt.D.ntypes.tg k v) (@GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
        (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) := by
  rw [← h.gen k]
  exact a.nt.A.grp.tg_tame k v
end GlobalTheory.CoefDuty.OPinModel
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.SerFinished
set_option maxHeartbeats 2000000 in
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  intro hP hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.coefficient_duty_pin_at_each_member hL) (_root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members hL))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hO, hC, -, -⟩
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    (_root_.GlobalTheory.CoefDuty.OPinModel.labFixed_iff_alt c.a).2 hO.lab
  have htame : ∀ D', D' = withLoc c.a.nt.L → ∀ k (v : D'.nd.PlG k),
      ∃ κ : IsLocalRing.ResidueField (D'.nd.plOm.1 (D'.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D'.host.g k),
        TameCoupled (D'.nd.plOm.1 (D'.naut.plGw k v)) κ (D'.ntypes.tg k v)
          (@GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩).gen := by
    rintro _ rfl k v
    exact ⟨c.a.nt.A.grp.kv k v, _root_.GlobalTheory.CoefDuty.OPinModel.labDat_gen_tame_at_plGw hO k v⟩
  refine _root_.UpperTheory.Lit.Dz.compatibleSystemLocalProperty hP.what₂ hP.green hP.zel hL (w.D Z) P _ hlab (htame _ c.a.nt.eq) ?_
  rw [hPin.M_eq]
  exact hC
end GlobalTheory.SerFinished
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serLoc_at_member_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  first | exact @_root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTameLabelMu
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiUnrAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiUnrAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TupleCharAtType
theorem xi_unrAt_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) :
    (P.tp.xi (D.nd.mu i)).UnrAt (D.naut.plGw k v) := by
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hgp := D.host.g_prime k
  rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]
  have hdel : (P.cf.delAt (D.nd.l i)).UnrAt (D.naut.plGw k v) := by
    unfold CharFrame.delAt
    split_ifs
    · exact P.cf.isDel'.unr _ (natCast_notMem hgp D.host.pde'_prime (D.host.pde_ne_g k).2.symm hwg)
    · exact P.cf.isDel.unr _ (natCast_notMem hgp D.host.pde_prime (D.host.pde_ne_g k).1.symm hwg)
  have hpsi : (P.tp.psi (D.nd.w i)).UnrAt (D.naut.plGw k v) := by
    have hψ := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
    by_cases hl : D.nd.l i = D.host.g k
    · intro x _
      refine hψ.atl _ ?_ x
      unfold OverP
      rw [D.nd.w_l i, hl]
      exact hwg
    · refine (hψ.ram _).2 ?_
      rw [← P.Q_eq i]
      have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
      have hS : D.naut.plGw k v ∈ D.nd.S i := by
        rw [D.nd.S_def i]
        refine ⟨?_, natCast_notMem hgp hlp (Ne.symm hl) hwg⟩
        fin_cases k
        · exact Or.inl hwg
        · exact Or.inr (Or.inl hwg)
      exact Finset.disjoint_left.mp (D.nd.SQ_disj i) hS
  intro x hx
  change (P.cf.delAt (D.nd.l i)).loc _ x * (P.tp.psi (D.nd.w i)).loc _ x = 1
  rw [hdel x hx, hpsi x hx, one_mul]
theorem mu_unit_value_eq_loc_k_mu0 : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal → (((S i _ hw).mu (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = (((P.cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro hL D P S hS i k v hw j hj u hu hnot
  rw [(hS.mu i _ hw j hj).2 (Units.mk0 (u : D.host.E) hu)]
  have hx := _root_.GlobalTheory.TupleCharAtType.xi_unrAt_alt P i k v _ (isUnitAt_of_notMem u hu hnot)
  show (((P.cf.mu0 j * P.tp.xi (D.nd.mu i)).loc (D.naut.plGw k v) (atFin _ (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = _
  change (((P.cf.mu0 j).loc _ (atFin _ (Units.mk0 (u : D.host.E) hu)) *
    (P.tp.xi (D.nd.mu i)).loc _ (atFin _ (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = _
  rw [hx, mul_one]
  rfl
end GlobalTheory.TupleCharAtType
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiUnrAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_mu_unit_eq_mu0_loc_k : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal → (((S i _ hw).mu (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = (((P.cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  exact _root_.GlobalTheory.TupleCharAtType.mu_unit_value_eq_loc_k_mu0
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.PendOf.tame_label_mu_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ChiTOk D P.cf → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  intro hP hL D P hchi S hS i k v hw
  obtain ⟨u, hu0, hunit, hrep⟩ := GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character D k v
  have hrep' : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u := by
    obtain ⟨ϖ, π, h1, h2, h3, h4⟩ := hrep
    exact ⟨D.nd.plOm.1 (D.naut.plGw k v), D.nd.plOm.2 (D.naut.plGw k v), D.ntypes.tg_mem k v, ϖ, π, h1, h2, h3,
      by rw [zpow_one]; exact h4⟩
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  obtain ⟨c, hc, hcv⟩ := hchi k v j u hu0 hrep'
  have htame := _root_.GlobalTheory.T.split_weil_mu_tame_of_is_true hL D P S hS i k v hw
  refine ⟨htame, (S i _ hw).mu_ok.1, c, hc, _root_.UpperTheory.Lit.Dz.dz_swap_compatible_alt hL D P.ty.grp k v _ _ htame u hu0 hrep c ?_⟩
  rw [_root_.GlobalTheory.T.split_mu_unit_eq_mu0_loc_k hL D P S hS i k v hw j (by simp only [j]; omega) u hu0 hunit]
  exact hcv.symm
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ChiTOk D P.cf → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  first | exact @_root_.GlobalTheory.PendOf.tame_label_mu_alt | exact _root_.GlobalTheory.PendOf.tame_label_mu_alt | (intros; apply _root_.GlobalTheory.PendOf.tame_label_mu_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesGoodOfLocalLanglands
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGoodRec
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Fc.GoodLinked
section Layer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
end Layer
end GlobalTheory.Fc.GoodLinked
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.Fc.GoodLinked
theorem row_goodRec_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    Row (sAnd (IsGoodE p.s) GoodRec) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition D _ _) => Formalism.BasicNotions.GoodFTAll D) :=
  RowE.row (RowE.of_all fun _ _ β _ _ _ q _ => q.2)
end GlobalTheory.Fc.GoodLinked
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.Fc.GoodLinked
section Layer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem goodFTAll_at_members_of_depthZero (h1 : GlobalTheory.GLq.Green) (h2 : GlobalTheory.Published.ZelevinskyPolynomialRing) :
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GoodFTAll (w.D Z) := by
  intro hL
  have hA := _root_.GlobalTheory.T.coefficient_duty_pin_at_each_member hL
  have hO := GlobalTheory.TypeVecConj.typeVec
  refine EvG.imp (EvG.inter hA hO) fun K _ _ _ _ h => ?_
  refine large₂.imp (large₂.inter h.1 h.2) fun B f T _ g => ?_
  intro hK w Z Wt p0 t nch n xd c _ _ hpin
  have hop := g.1 hK w Z Wt p0 t nch n xd c ‹_› ‹_› hpin
  have hrow := g.2 hK w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt
  refine _root_.UpperTheory.Lit.Dz.nonGaloisTwistType h1 h2 hL (w.D Z) _ nch n.tp c.a hop ?_
  have key : ∀ (D' : D7) (_ : D' = withLoc c.a.nt.L) (r' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r), HEq c.a.nt.rep r' →
      (∀ (I : GlobalTheory.TypeRec.Ident D') cp, GlobalTheory.TypeRec.IsComp I r' cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (G0g D'.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D' k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧
        ρ.asAlgebraHom D'.ntypes.e0 x = x) →
      ∀ (I : GlobalTheory.TypeRec.Ident c.a.nt.D) cp, GlobalTheory.TypeRec.IsComp I c.a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V)
        (_ : Module ℂ V) (ρ : Representation ℂ (G0g c.a.nt.D.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom c.a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom c.a.nt.D.ntypes.e0 x = x := by
    rintro _ rfl r' hr h
    have e : c.a.nt.rep = r' := eq_of_heq hr
    rw [e]
    intro I cp hc σ
    exact h ⟨I.i, I.cont⟩ cp hc σ
  exact key _ c.a.nt.eq _ c.row.rep_eq hrow
end Layer
end GlobalTheory.Fc.GoodLinked
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.Fc.GoodLinked
set_option maxHeartbeats 2000000 in
theorem largeBasePropertyG_goodRec_alt_alt (h1 : GlobalTheory.GLq.Green) (h2 : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP)
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) :
    GroupRetwisting.LargeBaseConditionG KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) GoodRec := by
  refine GlobalTheory.Mem.Top.EvG.imp (_root_.GlobalTheory.Fc.GoodLinked.goodFTAll_at_members_of_depthZero h1 h2 hL) fun K _ _ _ _ H => H.imp fun B f T _ t k C W V S' N G c q => ?_
  obtain ⟨w, Z, c', ⟨b, _⟩, e⟩ := q
  have key : ∀ x : Σ (C : Cols B) (Y : TC.Later B C), V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T,
      x = ⟨w.C, Z, c'⟩ → Formalism.BasicNotions.GoodFTAll (⟨B, x.1, x.2.1.W, x.2.1.V, x.2.1.S, x.2.1.N, x.2.1.G⟩ : Stages).toD7 := by
    rintro _ rfl
    exact t k w Z c'.Wt c'.O.p0 b.what₂ c'.O.nch b.n c'.O.xd b.nx.1 ((hN _ _ _ _ _ _ _ _ _ _ _ _ _ b.nx.2).map Prod.fst) ⟨b.rx⟩ b.pin
  exact key _ e
theorem linkedAt_goodFTAll : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D) :=
  fun h1 h2 hL N S Γ hN => LgModel.rowL_of_good (_root_.GlobalTheory.Fc.GoodLinked.largeBasePropertyG_goodRec_alt_alt h1 h2 hL N S Γ hN) (_root_.GlobalTheory.Fc.GoodLinked.row_goodRec_alt _)
theorem row_good_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) ∧
      _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowGoodnessCondition := by
  intro h1 h2 hL N S Γ hN
  refine ⟨_root_.GlobalTheory.Fc.GoodLinked.linkedAt_goodFTAll h1 h2 hL N S Γ hN, ?_⟩
  obtain ⟨R, hR, h⟩ := _root_.GlobalTheory.Fc.GoodLinked.linkedAt_goodFTAll h1 h2 hL N S Γ hN
  refine ⟨R, hR, h.imp fun _ _ _ key => ?_⟩
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => Ind.ev_of_atAll key Fm (w3_a hc)⟩⟩
end GlobalTheory.Fc.GoodLinked
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowGoodnessCondition := by
  first | exact @_root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt | exact _root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt | (intros; apply _root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt <;> assumption)
end
end
end
