module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfSeriesLocal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.DzGoodVec
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant GlobalTheory.TypeLeaf
namespace DiscreteGroups.sglob.DzType.Rt

theorem good_of_vector_row_m : ∀ (D : D7) (Rw : GlobalTheory.HeightCounting.RowSide D) (L : ∀ k, LabelDatum (D.host.g k)) (rc : GlobalTheory.SerSys.Corr D) (cp : GlobalTheory.GoodTypes.Comp D), LabTie D L → DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc → (∀ k v, GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.GoodTypes.SeriesConj D → (∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (σ : D.what₂.FT), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) → ∀ x : V, x ≠ 0 → (∀ a, ρ.asAlgebraHom a x ∈ W) → ρ.asAlgebraHom D.ntypes.e0 x = x → D.nd.goodRow σ := by
  intro D Rw L rc cp hT hLP hCl hC hP V _ _ ρ W σ hW x hx hxW he
  obtain ⟨t, a, ht, h0, hfix⟩ := GlobalTheory.GoodTypes.exists_good D ρ hx he
  have key : ∀ k v, GlobalTheory.SeriesSupportTest.dualFun D k (t k v) = D.nd.lab k σ v := by
    intro k v
    have hl : IsLabel D k (t k v) := (ht k).1.1 v
    have h1 := hfix k v
    rw [GlobalTheory.GoodTypes.act_atPlace] at h1
    have h2 := (hW k v).act_ne _ (D.ntypes.eSer k (dualLab D k (t k v))) (fun y => by
      rw [← GlobalTheory.GoodTypes.labAct_conj D k hl, ← hC k _ hl, Finsupp.mapRange_apply]; rfl) (hxW a) h0 h1
    obtain ⟨p1, p3⟩ := hP σ k v
    have q1 := ((hCl k v) _ _ p1).1
    rw [(hT k).2] at h2
    have h3 := hLP k v D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) (cp σ k v) p1 _ h2
    rw [(hT k).1] at h3
    simp only [] at h3
    rw [← p3] at h3 q1
    rw [D.ntypes.inertiaCharpoly_type k v _ (by rw [← Rw.lab_eq, q1, (D.nd.lab_monic k σ v).2]), ← Rw.lab_eq] at h3
    rw [GlobalTheory.SeriesSupportTest.dualFun, if_pos hl]
    exact GlobalTheory.GoodTypes.eq_of_teich _ (GlobalTheory.Compare.TeichmullerRoots.teich_injective _ (D.ntypes.teichC_inj k))
      (GlobalTheory.SeriesSupportTest.label_dual D k hl).1 (D.nd.lab_monic k σ v).1 h3.symm
  have hd := GlobalTheory.SeriesSupportTest.good_dualFun D t ht
  simp only [key] at hd
  exact hd

end DiscreteGroups.sglob.DzType.Rt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllOfLocal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsClassMapCorrespondence
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRc_classMap_correspondence : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D), ∃ rc : GlobalTheory.SerSys.Corr D, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc ∧ ∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v) := by
  first | exact @_root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt | exact _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt | (intros; apply _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
theorem goodFTAll_of_local_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → LabTie D L → (∀ k, TameGen.DepthZeroCuspidal (D.host.g k)) → (∀ (I : Ident D) rc, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, DiscreteGroups.sglob.DzType.Rt.TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2)) → (∀ (I : Ident D) cp, IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hL D T Rw rep L hRow hDep hLT hDZ hTP hVec σ
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := _root_.GlobalTheory.T.exists_isRc_classMap_correspondence hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc hL D T I rc hrc Rw rep hRow hDep
  have hP : DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc :=
    DiscreteGroups.sglob.DzType.Rt.labParamLe_of D L rc hG (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D T I rc hrc) hDZ (hTP I rc hrc)
  have hSC := GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree hG D L hLT
  obtain ⟨V, _, _, ρ, W, x, hconj, hx0, hxW, hxe⟩ := hVec I cp hcomp σ
  exact _root_.DiscreteGroups.sglob.DzType.Rt.good_of_vector_row_m D Rw L rc cp hLT hP hcls hSC hcp V ρ W σ hconj x hx0 hxW hxe
end DiscreteGroups.sglob.DzType.Rt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentationComponent
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
set_option maxHeartbeats 2000000 in
theorem goodFTAll_pinned_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hDZ hL D cf nch tp a hp hloc
  have h0 : GoodFTAll a.nt.D := by
    refine _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_of_local_alt hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.row a.depth hp.lab
      (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) ?_ hloc
    intro I rc hrc k v
    refine _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL a.nt.D a.nt.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) k v (a.nt.A.grp.kv k v) ?_
    rw [← hp.gen k]
    exact a.nt.A.grp.tg_tame k v
  have e : ∀ D', D' = withLoc a.nt.L → GoodFTAll D' := by
    rintro _ rfl
    exact h0
  exact e D a.nt.eq
set_option maxHeartbeats 1000000 in
theorem exists_representation_component_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_pinned_alt
end DiscreteGroups.sglob.DzType.Rt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllStA
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
set_option maxHeartbeats 2000000 in
theorem goodFTAll_stA_alt (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) (hlab : GlobalTheory.CoefDuty.OPinModel.LabFixed D)
    (hloc : ∀ (I : GlobalTheory.TypeRec.Ident D) cp, GlobalTheory.TypeRec.IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) : GoodFTAll D := by
  refine _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_of_local_alt hG hZ hL D a.A.wdT a.A.row rep
    (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) a.row a.depth hlab
    (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (D.host.g k) ⟨D.host.g_prime k⟩) ?_ hloc
  intro I rc hrc k v
  refine _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D a.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) k v (a.A.grp.kv k v) ?_
  rw [← a.zeta k]
  exact a.A.grp.tg_tame k v
end DiscreteGroups.sglob.DzType.Rt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTruthOfLabelTie
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem rowTruth_of_labelTie_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep :=
  _root_.DiscreteGroups.sglob.DzType.Rt.typeLab_of_local_m_alt
end DiscreteGroups.sglob.DzType.Rt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameUniformizerPower
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzValue
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DepthZeroRankOneLabel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
theorem character_inertia_eq_of_congruent_generator [_root_.NumberField.IsTotallyComplex E] (H : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt) {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} {rc : IrrGL (k := w.adicCompletion E) → WD h} (hl : _root_.UpperTheory.One.M.LawsM a ha ε rc)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : GlobalTheory.GLq.LabelDatum g) (t : G E Ω) (ht : t ∈ Ine (F := E) A)
    (hT : TameCoupled A κ t L.gen) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ)
    (htm : GlobalTheory.SplitWeil.IsTame μ) (n : ℕ) (hn : n.Coprime g)
    (hgen : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (n : ZMod g) = L.gen 1) (x : (w.adicCompletion E)ˣ)
    (hx : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - (n : w.adicCompletion E)) < 1) :
    μ (a (ineIncl h ⟨t, ht⟩)) = μ x := by
  haveI : IsLocalHom (PadicInt.toZMod (p := g)) := IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
  let u₀ : (ZMod g)ˣ := ZMod.unitOfCoprime n hn
  have hu₀ : IsUnit ((n : ℕ) : ℤ_[g]) := isUnit_of_map_unit (PadicInt.toZMod (p := g)) _ (by
    rw [map_natCast]; exact u₀.isUnit)
  obtain ⟨θ, hθ⟩ := exists_red i hi hw μ htm
  obtain ⟨P, hP, e⟩ := GlobalTheory.Published.DepthZeroModel.exists_label L θ u₀ (by rw [ZMod.coe_unitOfCoprime]; exact hgen)
  have h1 := H E Ω g A w h rc (_root_.UpperTheory.One.M.New.close hl) i hi κ L t ht hT 1 (Or.inl rfl) (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)
    (IrrGL.isCusp_ofChar μ hμ) _ P hP (inflates_units i θ μ hμ hθ)
  have h2 : rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)) = _ := hl.one μ hμ
  rw [h2, e, WD.inePol_of_mem_Ine _ ht, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd] at h1
  have h3 := congrArg (fun p => p.coeff 0) h1
  have h4 : μ (a (ineIncl h ⟨t, ht⟩)) = θ u₀ := Units.ext (by simpa using h3)
  have h5 : u₀ = Units.map (PadicInt.toZMod (p := g)).toMonoidHom hu₀.unit := Units.ext (by simp [u₀])
  rw [h4, h5, hθ]
  set y : (w.adicCompletion E)ˣ :=
    Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hu₀.unit) with hy
  have hyn : (y : w.adicCompletion E) = n := by simp [hy]
  have hyi : valuation (w.adicCompletion E) ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
    have e4 : ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        i (((hu₀.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) : ℚ_[g]) := by
      rw [hy, ← map_inv, ← map_inv]; rfl
    rw [e4]; exact val_int_le i hi _
  have h6 : μ (x * y⁻¹) = 1 := htm _ (by
    have e3 : ((x * y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((x : w.adicCompletion E) - n) * ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [← hyn, sub_mul, Units.mul_inv]; simp
    rw [e3, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hyi)
  rw [map_mul, map_inv, mul_inv_eq_one] at h6
  exact h6.symm
end DiscreteGroups.sglob.DzType.Rt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRankOne
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroRankOneLabel
open ValuativeRel
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
open GlobalTheory.TameRes
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
end GlobalTheory.DepthZeroRankOneLabel
open GlobalTheory.WeilDeligne in
theorem GlobalTheory.DepthZeroRankOneLabel.wild_trivial_m_alt (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (hT : GlobalTheory.SplitWeil.IsTame μ)
    (a : Weil (D.nd.plOm.2 (D.naut.plGw k v)) →* ((D.naut.plGw k v).adicCompletion D.host.E)ˣ)
    (ha : GlobalTheory.LocLanglands.IsLocalArtin (D.nd.plOm.2 (D.naut.plGw k v)) a)
    (ε : GlobalTheory.LocLanglands.EpsFamily (D.nd.plOm.1 (D.naut.plGw k v)))
    (rc : GlobalTheory.LocGL.IrrGL (k := (D.naut.plGw k v).adicCompletion D.host.E) → WD (D.nd.plOm.2 (D.naut.plGw k v)))
    (hl : _root_.UpperTheory.One.M.LawsM a ha ε rc) :
    ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 := by
  have htame := GlobalTheory.SerSys.LabDepth.tame_of_isTameWD (_root_.UpperTheory.One.M.LawsM.depth hl (GlobalTheory.LocGL.IrrGL.ofChar μ hμ) (UpperTheory.One.M.good_ofChar μ hμ) (by
    refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv
      (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep (Irr.ofDet 1 μ hμ).toIrrRep).some.symm ?_
    refine (Submodule.ne_bot_iff _).2 ⟨(show (Irr.ofDet 1 μ hμ).V from (1 : ℂ)), GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_,
      (one_ne_zero : (1 : ℂ) ≠ 0)⟩
    have hu' : u ∈ GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin 1) := hu
    have h1 := GlobalTheory.StepData.mem_KOne.1 hu' 0 0
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h1
    have h2 : μ (Matrix.GeneralLinearGroup.det u) = 1 := hT _ (by
      have e : ((Matrix.GeneralLinearGroup.det u : (_)ˣ) : (D.naut.plGw k v).adicCompletion D.host.E) = u.val 0 0 := by
        simp [Matrix.det_fin_one]
      rw [e]; exact h1)
    change (GlobalTheory.SmGL.detRep (Fin 1) μ) u (1 : ℂ) = (1 : ℂ)
    simp [GlobalTheory.SmGL.detRep, h2]))
  rw [hl.one, WD.lpOfChar, WD.tame_mk] at htame
  intro σ hσ
  have h2 := LinearMap.congr_fun (htame σ hσ) (fun _ => 1)
  have h3 := congrFun h2 0
  simpa using h3
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DepthZeroRankOneLabel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
theorem lab_eq_of_tameRep_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c := by
  intro hDZ hL D Γ k v μ hμ hT u hu hex c hc
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, hε, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hSet : GlobalTheory.WeilDeligne.TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k)
      (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have e1 : _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 μ hμ) =
      GlobalTheory.WeilDeligne.WD.lpOfChar _ (μ.comp a) (ha.smooth hμ) := hl.one μ hμ
  have hwild : ∀ σ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ GlobalTheory.WeilDeligne.Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 :=
    _root_.GlobalTheory.DepthZeroRankOneLabel.wild_trivial_m_alt D k v μ hμ hT a ha ε _ hl
  have hval : μ (a ⟨D.ntypes.tg k v, GlobalTheory.WeilDeligne.Ine_le_Weil _ hSet.2.1⟩) =
      μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) := by
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hw := D.naut.plGw_over k v
    have hN := GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw
    have hw2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal ^ 2 := fun h2 => by
      have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast (D.host.g_prime k).ne_zero
      have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
        (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
      have := hs (D.naut.plGw k v).asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h2)
      exact (D.naut.plGw k v).isPrime.ne_top (Ideal.isUnit_iff.1 this)
    obtain ⟨ϖ, π, hϖ, hϖ2, hπ, hv⟩ := hex
    obtain ⟨n, hn, hun, hgen⟩ := GlobalTheory.DepthZeroRankOneLabel.residue_of_cong _ _ _ (D.nd.plOm.2 _) hN hw hw2
      (Γ.kv k v) _ (Γ.ζ k) (D.ntypes.tg_mem k v) (Γ.ζ_gen k) (Γ.tg_tame k v) u ϖ π hϖ hϖ2 hπ hv
    have hx := GlobalTheory.DepthZeroRankOneLabel.val_lt_of_mem hun
    exact _root_.DiscreteGroups.sglob.DzType.Rt.character_inertia_eq_of_congruent_generator hDZ hl (I.i k v) (I.cont k v) hw (Γ.kv k v)
      (GlobalTheory.DepthZeroRankOneLabel.labDatum (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
      _ (D.ntypes.tg_mem k v) (Γ.tg_tame k v) μ hμ hT n hn hgen _ (by simpa using hx)
  unfold _root_.GlobalTheory.PendOf.localLabelPolynomial
  rw [e1, GlobalTheory.WeilDeligne.WD.lab_lpOfChar_eq_iff hSet _ hwild c, hc, MonoidHom.comp_apply, hval]
set_option maxHeartbeats 1000000 in
theorem tame_uniformizer_power_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c :=
  _root_.DiscreteGroups.sglob.DzType.Rt.lab_eq_of_tameRep_alt
end DiscreteGroups.sglob.DzType.Rt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfRegularLocal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RegularLocalOfGreenLabel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InePolOfHas
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
section Loc
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory GlobalTheory.RegType
variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ
theorem inePol_eq_liftPoly_of_cuspidal {n : ℕ} (hn : 0 < n) (hbig : n = 1 ∨ 16 * n ^ 2 < g) (σ : Irr (w.adicCompletion E) n) (hc : IsCuspidal σ.π) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (σ.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls σ.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  have hc' : IsCuspidal (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap i.symm hi σ.π hc
  let ρ : GLRep g := ⟨n, Rep.of (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))⟩
  have hρ : TameGen.IsSC ρ := ⟨hn, (Model.isIrrRep_iff _).2 (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp σ.irr _
      fun y => ⟨_, GlobalTheory.TameRecord.glMap_apply_symm i y⟩), GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal _ _ _ _ hc'⟩
  obtain ⟨τ, φ, hs, hinj, heq, he⟩ := TameGen.exists_simple_of_has (sysOf L h5 hA) ρ.2.ρ f hf
  have hφ : (fixK1 ρ.2.ρ).subtype ∘ₗ φ ≠ 0 := fun e => by
    have h0 : ∀ u : τ, u = 0 := fun u => hinj (Subtype.ext (by simpa using LinearMap.congr_fun e u))
    exact CategoryTheory.id_nonzero τ (by ext u; exact (h0 _).trans (h0 _).symm)
  have hfix : fixK1 ρ.2.ρ ≠ ⊥ := fun e => hφ (LinearMap.ext fun u => (Submodule.eq_bot_iff _).1 e _ (φ u).2)
  have hτ : FiniteGL.IsCuspidal τ.ρ := fun b hb hb' u hu => hinj (by
    rw [map_zero]
    exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal g ρ hρ hfix b hb hb' _ fun x hx => by rw [← heq, hu x hx])
  refine hDZ E Ω g A w h rc hrc i hi κ L t ht hκ n hbig σ.toIrrRep (IrrGL.isCusp_of.2 ⟨hn, hc⟩) τ f
    (isCuspOf_of_series L h5 hA τ (TameGen.isCusp_character hn τ hs hτ) f he) ⟨_, hφ, fun k u => ?_⟩
  exact (congrArg Subtype.val (heq (red g n k) u)).trans (repK_red ρ.2.ρ k (φ u))
theorem inePol_eq_liftPoly_of_has (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma) {n : ℕ}
    (π : Irr (w.adicCompletion E) n) (hB : 16 * n ^ 2 < g) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (π.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls π.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  obtain ⟨s, d, σ, hs⟩ := GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL hBZ hGL _ n π
  have h1 := hrc.recSupp n s π d σ hs (ineIncl h ⟨t, ht⟩)
  obtain ⟨-, hc, e, U, T, hT⟩ := hs
  obtain ⟨φ⟩ := GlobalTheory.IndField.multiProd_comp_glMap i.symm hi' hi
    (GlobalTheory.SplitWeil.nabs_map_of_homeomorph i.symm hi' hi) e (fun a => (σ a).π)
  have h2 : IsSubquotient (π.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))
      ((multiProd e fun a => (σ a).π).comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    ⟨⟨U.toSubmodule, fun x _ hv => U.apply_mem_toSubmodule _ hv⟩, ⟨T.toLinearMap, fun x => T.isIntertwining' _⟩, hT⟩
  obtain ⟨fs, hfs, rfl⟩ := series_of_isSubquotient (sysOf L h5 hA) e
    (fun a => (σ a).π.comp (Matrix.GeneralLinearGroup.map (n := Fin (d a)) i.toRingHom))
    (h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)) f hf
  have hbig : ∀ a, d a = 1 ∨ 16 * d a ^ 2 < g := fun a =>
    Or.inr (lt_of_le_of_lt (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (DiscreteGroups.sglob.DzType.Rt.le_of_sigmaEquiv e a) 2)) hB)
  have h3 : ∀ a, (rc (cls (σ a).toIrrRep)).charPol (ineIncl h ⟨t, ht⟩) = TameGen.liftPoly L.teich (fs a) := fun a => by
    rw [← WD.inePol_of_mem_Ine _ ht]
    exact _root_.DiscreteGroups.sglob.DzType.Rt.inePol_eq_liftPoly_of_cuspidal i hi hrc hDZ κ L h5 hA ht hκ (hc a).1 (hbig a) (σ a) (hc a).2.2 _ (hfs a)
  have h4 : ∀ u : Finset (Fin s), TameGen.liftPoly L.teich (∏ a ∈ u, fs a) = ∏ a ∈ u, TameGen.liftPoly L.teich (fs a) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp [TameGen.liftPoly_one]
    | insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, TameGen.liftPoly_mul _ (TameGen.Has.monic (hfs a)).ne_zero
        (monic_prod_of_monic _ _ fun b _ => TameGen.Has.monic (hfs b)).ne_zero, ih]
  rw [WD.inePol_of_mem_Ine _ ht, h4]
  exact h1.trans (Finset.prod_congr rfl fun a _ => h3 a)
end Loc
end DiscreteGroups.sglob.DzType.Rt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
section Loc
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory GlobalTheory.RegType
variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ
end Loc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne in
theorem regLoc_of_greenLab : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D := by
  intro hP hDZ hL D Γ hG k v π ρ f hρ hsq ⟨x, hx, hnk⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
  have hrc := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hw := D.naut.plGw_over k v
  have hA := GlobalTheory.RegType.allLab (Γ.O k) (hG k)
  have h5 := GlobalTheory.SerSys.Bridge.five_le D k
  have hx' := GlobalTheory.RegType.mem_principalCongruenceFixed_of_levelOne hw (I.i k v) (I.cont k v) π.π hx
  have hz := GlobalTheory.RegType.actK_ne_of_notKilled hw (I.i k v) (I.cont k v) π.π hx _ hnk
  have he := GlobalTheory.RegType.eSerC_mul_zIdem (Γ.O k) (hG k) ρ hρ.1 f (by rw [← Γ.eSer_def k f]; exact hρ.2)
  have hHas := GlobalTheory.RegType.has_of_actK (GlobalTheory.RegType.sysOf _ h5 hA) _ hx' hz he
  have hine : (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) D.R.r π).inePol (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod :=
    _root_.DiscreteGroups.sglob.DzType.Rt.inePol_eq_liftPoly_of_has (I.i k v) (I.cont k v) hrc hDZ (Γ.kv k v) _ h5 hA (D.ntypes.tg_mem k v)
      (Γ.tg_tame k v) hP.bz hP.geo π (DiscreteGroups.sglob.DzType.sixteen_sq_lt_g D k) f hHas
  refine ⟨WD.noMonodromy_of_inertia_separable_charpoly _ _ _ _ _ _ _ (D.ntypes.tg_mem k v) ?_, ?_⟩
  · rw [hine]
    exact GlobalTheory.GoodRowMono.separable_prod_teich _ (D.ntypes.teichC_inj k) hsq
  · have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
        (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
    have htame : (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) D.R.r π).tame := by
      first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := hrc
      refine GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((fun hx => haveI := UpperTheory.One.M.charZero_compl (D.naut.plGw k v); _root_.UpperTheory.One.M.LawsM.depth hl _ (UpperTheory.One.M.good_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ _ hx) hx : _ → _) ?_)
      refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep π.toIrrRep).some.symm ?_
      refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => hx u fun a b => ?_, fun h0 => hz ?_⟩
      · have := GlobalTheory.StepData.mem_KOne.1 hu a b
        rwa [Matrix.sub_apply, Matrix.one_apply] at this
      · rw [h0, map_zero]
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [_root_.GlobalTheory.PendOf.localLabelPolynomial, WD.lab_eq_iff_of_tame hSet htame, hine, e1, roots_multiset_prod_X_sub_C]
    exact ⟨GlobalTheory.SerSys.TameGen.Has.monic hHas, rfl⟩
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
section Loc
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory GlobalTheory.RegType
variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ
end Loc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem regLoc_of_depth_zero_inertia_big_greenLab : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.regLoc_of_greenLab
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalProperty
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTypeSplitProp
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.BlockTypeSplitThirdPlace : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalPropertyExplicit
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.SerSys.Assembly
abbrev _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
      TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) →
    GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D
end GlobalTheory.SerSys.Assembly
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelTameCharacter
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType ValuativeRel Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open NumberField IsDedekindDomain GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel GlobalTheory.TameCharLabel
theorem label_reduction_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u := by
  intro H hL D Γ k v χ hχ u htame hlab
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have hp : resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k := by
    haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨h1, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    apply (GlobalTheory.LocLanglands.resCard_eq_normV _).trans
    simpa [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1
  refine ⟨hp, fun L hteich hgen => ?_⟩
  obtain ⟨θ, hθ⟩ := exists_charLift hp htame
  set x := _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    (GlobalTheory.LocLanglands.cls (IrrRep.det (Fin 1) χ hχ)) with hx
  have hlab' : GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) x = X - C u := hlab
  refine ⟨θ, hθ, fun hu0 => ?_, fun u' hu' => ?_⟩
  · have := GlobalTheory.WeilDeligne.WD.lab_coeff_zero_ne_zero (D.ntypes.teichC k) (D.ntypes.tg k v) x
    rw [hlab', hu0] at this
    simp at this
  · obtain ⟨I⟩ := GlobalTheory.TypeIdent.nonempty_ident D
    obtain ⟨P, hP, hPe⟩ := exists_label L θ u' hu'
    have hT : Formalism.L2.NT.TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (Γ.kv k v) (D.ntypes.tg k v) L.gen := by
      rw [hgen]; exact Γ.tg_tame k v
    have h1 := H D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
      (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) (I.i k v) (I.cont k v) (Γ.kv k v) L _ (D.ntypes.tg_mem k v) hT 1 (Or.inl rfl)
      (IrrRep.det (Fin 1) χ hχ) (GlobalTheory.LocGL.IrrGL.isCusp_ofChar χ hχ) (tauOne θ) P hP
      (inflates_det (I.i k v) (I.cont k v) hχ hθ)
    rw [hPe] at h1
    first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    have hdim : x.lpDim = 1 := hl.dim _
    have h2 := GlobalTheory.WeilDeligne.WD.inePol_eq_of_natDegree_lab (D.ntypes.teichC k) (D.ntypes.tg k v) x
      (by rw [hlab', hdim, natDegree_X_sub_C])
    have hr : Formalism.CyclotomicNorms.rootsBar (X - C u) = {algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) u} := by
      simp [Formalism.CyclotomicNorms.rootsBar]
    rw [hlab', hr, h1] at h2
    have h3 := congrArg (fun q => q.coeff 0) h2
    simp at h3
    rw [hteich]
    exact h3
set_option maxHeartbeats 1000000 in
theorem labAt_ofDet_tame_eq_X_sub_C : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u :=
  _root_.DiscreteGroups.sglob.DzType.Rt.label_reduction_alt
end DiscreteGroups.sglob.DzType.Rt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalBesselMultiplicityOne
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.LocalBesselMultiplicityOne' : Prop :=  Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjSelfDualGaloisRepCMDatum
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace : Prop :=  ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionAllStages
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GoodFirst
set_option maxHeartbeats 2000000 in
abbrev _root_.GlobalTheory.GoodFirst.FirstTermConditionAllStagesAlt : Prop := ∀ (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) (hlab : GlobalTheory.CoefDuty.OPinModel.LabFixed D)
    (hloc : ∀ (I : GlobalTheory.TypeRec.Ident D) cp, GlobalTheory.TypeRec.IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x),  GoodFTAll D
end GlobalTheory.GoodFirst
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibilityCMDatum
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum' : Prop :=  ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTwistType
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.NonGaloisTwistType' : Prop :=  GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
namespace UpperTheory.Lit.Dz
theorem dz_swap_compatible_alt : _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.tame_uniformizer_power_alt (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localGlobalCompatibility_cmDatum_alt : _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum' :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.labAt_ofDet_tame_eq_X_sub_C (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem blockTypeSplitProp : _root_.GlobalTheory.T.BlockTypeSplitThirdPlace :=
  fun a hL => _root_.DiscreteGroups.sglob.DzType.Rt.regLoc_of_depth_zero_inertia_big_greenLab a (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem nonGaloisTwistType : _root_.GlobalTheory.T.NonGaloisTwistType' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.exists_representation_component_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem firstTermCondition_all_stages : _root_.GlobalTheory.GoodFirst.FirstTermConditionAllStagesAlt :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_stA_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty : _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.serLoc_of_tame_coupled_and_cenLoc a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty_explicit : _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.depthZeroType_series_local_explicit_alt a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localBesselMultiplicityOne : _root_.GlobalTheory.T.LocalBesselMultiplicityOne' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.rowTruth_of_labelTie_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
end UpperTheory.Lit.Dz
end
end
