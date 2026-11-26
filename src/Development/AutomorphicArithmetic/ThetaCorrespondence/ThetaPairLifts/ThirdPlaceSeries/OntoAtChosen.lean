module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosen
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosen
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem onto_at_chosen_alt : _root_.GlobalTheory.BigOn.SurjectiveOntoX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ →
    EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 σ :=
  fun h 𝒜 σ hD hR hM =>
    _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigOn.More p)
      (fun C CH _ _ _ p => (p.S false).ON (p.N C CH)) h 𝒜 σ hD hR hM
end GlobalTheory.Fc.Ind
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosenStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_norm_bound_of_more_points : _root_.GlobalTheory.BigOn.SurjectiveOntoX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt | exact _root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootAltBis
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
def ScaleRootAltBis : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P ≠ 0 →
    ∃ n : ℕ, n ≠ 0 ∧ ν' ^ n = ν ^ n
def CoordinateRangeCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν μ : ℂ), ν ≠ 0 →
  ∀ f f', f ≠ 0 → rdAt p w j hρ ν f' = μ • rdAt p w j hρ ν f →
    ∃ u, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) u = μ
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventualL6OfLowerScalar
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventualL6OfLowerScalar
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem eventual_L6_of_lower_scalar_alt : _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL6Bound 𝒜 σ := by
  intro h 𝒜 σ hd hr
  have hG : EvW (_root_.GlobalTheory.Fc.Ind.conditionOnPoint fun _ _ _ _ => True) 𝒜 σ :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ _ => ⟨0, fun _ _ _ _ => trivial⟩
  have key := _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun _ => True) (fun _ _ _ _ => True) lowScalarPt ?_ 𝒜 σ hd hr hG
  · exact key
  · obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := h e he hle
    refine ⟨K, fun Fm CH hc hL _ => ⟨0, le_rfl, ?_⟩⟩
    obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
    exact ⟨x0, fun x hx hle i p hp _ C _ => hx0 x hx hle i p hp C⟩
end GlobalTheory.Fc.Ind
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventualL6OfLowerScalarStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_L6_bound_of_lamLow : _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL6Bound 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar_alt | exact _root_.GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.eventual_L6_of_lower_scalar_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricDatumOfFamily
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EZeroThetaDescentEvalAltBisStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EZeroThetaDescentEvalAltAlt2
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GoodFix
open _root_.Formalism.L2.DIV
end GlobalTheory.GoodFix
namespace GlobalTheory.GoodFix
open _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev
end GlobalTheory.GoodFix
namespace GlobalTheory.GoodFix
open _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev
end GlobalTheory.GoodFix
open GlobalTheory.GoodFix in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.GoodFix.e_zero_theta_descent_eval_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) (v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec), (_root_.GlobalTheory.Fam.pk_z W).e0 ((_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v)) = (_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F v
  have hC := hP.bot.hyp.2.2.2.1
  have hL := hP.lev
  unfold _root_.GlobalTheory.MiS.LevelHypothesis at hL
  obtain ⟨⟨s, hs⟩, -⟩ := hL
  have hgf := good_fix (W.P.A3.A.fam.R t) (W.P.A3.A.fam.lvl W.Q.F.P1 W.Q.F.ψ1) hs.ok2.irr F
  exact goodProjector_fixes_compositeThetaLift_of_fixed GlobalTheory.T.cusp_forms_rapid_decay (_root_.GlobalTheory.Fam.pk_z W) hC.lev hC.models hC.chain hC.grp.red_R t _ hgf v
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e_zero_theta_descent_eval_alt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) (v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec), (_root_.GlobalTheory.Fam.pk_z W).e0 ((_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v)) = (_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v) := by
  first | exact @_root_.GlobalTheory.GoodFix.e_zero_theta_descent_eval_alt_bis | exact _root_.GlobalTheory.GoodFix.e_zero_theta_descent_eval_alt_bis | (intros; apply _root_.GlobalTheory.GoodFix.e_zero_theta_descent_eval_alt_bis <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopOfMemCXP
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopOfMemCXP
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopLevelP
section Package
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Package
theorem vector_of_mem_cxp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  obtain ⟨⟨s, hs⟩, -⟩ := hP.lev
  exact mem_CXP_of_good (_root_.GlobalTheory.Fam.pk_z W) hC.grp.red_R hC.models.jX hC.models.cX hs.ok2.irr W.Q.F.P1 W.Q.F.ψ1 t
    (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ⟨F, rfl⟩ ((hP.hTop t).le ⟨_, rfl⟩)
end GlobalTheory.TopLevelP
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopOfMemCXPStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_of_mem_extra_projection : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t := by
  first | exact @_root_.GlobalTheory.TopLevelP.vector_of_mem_cxp | exact _root_.GlobalTheory.TopLevelP.vector_of_mem_cxp | (intros; apply _root_.GlobalTheory.TopLevelP.vector_of_mem_cxp <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricDatumOfFamily
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowDescent
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev geometricDatumOfFamily (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H :=
  (_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)
theorem apex_eq_toMap_geometricDatum (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) :
    _root_.GlobalTheory.Fam.leadingLinearMap W t F = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F)) := rfl
theorem dn_fst_eq_dnFrom_fst {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) :
    ∀ k, k + 1 ≤ D.R.m → ∀ (F : (f.t t).CC k) (F' : (_root_.GlobalTheory.Fam.pk_z W).CC t k), F.1 = F'.1 →
      ((f.t t).dn k F).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k F').1 := by
  intro k
  induction k with
  | zero => intro _ F F' e; exact e
  | succ k ih =>
    intro hk F F' e
    obtain ⟨h1, h2⟩ := hr.io k (by omega) F
    have e2 : (⟨F.1, h1⟩ : (_root_.GlobalTheory.Fam.pk_z W).CC t (k + 1)) = F' := Subtype.ext e
    show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k ((_root_.GlobalTheory.Fam.pk_z W).ioY t k F')).1
    rw [← e2]
    exact ih (by omega) _ _ h2
theorem dnFrom_fst_eq_of_heq (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {k : ℕ} (hk : D.R.m - 1 = k) (X : (_root_.GlobalTheory.Fam.pk_z W).CC t k) (X' : (_root_.GlobalTheory.Fam.pk_z W).CC t (D.R.m - 1))
    (e : HEq X X') : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k X).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) X').1 := by
  subst hk
  rw [eq_of_heq e]
theorem heq_eq_rec_apply (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {M : Type} [AddCommGroup M] [Module ℂ M] {k k' : ℕ} (p : k = k')
    (g : M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t k) (z : M) :
    HEq ((Eq.rec (motive := fun n _ => M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t n) g p) z) (g z) := by
  subst p
  rfl
set_option maxHeartbeats 1000000 in
theorem down_eq_thDn {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) (n : ℕ)
    (h : 2 * n + 2 * 0 + 2 = D.R.m) (G : (f.t t).CT) (y : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H)
    (hG : G.1 = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e y)) : _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := by
  have H := hr.ioT (2 * n) h G
  have h' := H.choose
  have e : (((f.row t).ioT (2 * n) h G).1 : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) =
      (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩).1 := H.choose_spec
  have e1 := _root_.GlobalTheory.RowDescent.dn_fst_eq_dnFrom_fst f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) e
  have hy : (⟨G.1, h'⟩ : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)) =
      ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e).rangeRestrict y := Subtype.ext hG
  have e2 := _root_.GlobalTheory.RowDescent.dnFrom_fst_eq_of_heq W t (idx_top h) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)
    (_root_.GlobalTheory.RowDescent.heq_eq_rec_apply W t (idx_top h) ((_root_.GlobalTheory.Fam.pk_z W).ioX t) _)
  have e3 : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y :=
    (congrArg (fun z => (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t z)).1) hy).trans
      (GlobalTheory.ChainEquiv.thDn_eq t y).symm
  have key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := e1.trans (e2.trans e3)
  unfold _root_.GlobalTheory.MiTop.descentToLevelZero
  exact key
theorem piTensorProduct_lift_postOn_eq_of_fixed (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (T : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ))
    (hT : ∀ v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec, (_root_.GlobalTheory.Fam.pk_z W).e0 (T (PiTensorProduct.tprod ℂ v)) = T (PiTensorProduct.tprod ℂ v)) :
    PiTensorProduct.lift (postOn ((_root_.GlobalTheory.Fam.pk_z W).MY 0) (_root_.GlobalTheory.Fam.pk_z W).e0 (PiTensorProduct.lift.symm T)) = T := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]
  rw [show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]
end GlobalTheory.RowDescent
end
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MiTop.linkDown_of_ok : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkDescends f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F
  have hChar := hP.bot.hyp.2.2.2.1
  obtain ⟨⟨s, hs⟩, -⟩ := hP.lev
  have hMem : _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈
      CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t :=
    GlobalTheory.TopLevelP.mem_CXP_of_good (_root_.GlobalTheory.Fam.pk_z W)
      hChar.grp.red_R hChar.models.jX hChar.models.cX hs.ok2.irr W.Q.F.P1 W.Q.F.ψ1 t
      (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ⟨F, rfl⟩
      ((hP.hTop t).le ⟨_, rfl⟩)
  refine ⟨⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, hMem⟩, rfl, ?_⟩
  have e1 := _root_.GlobalTheory.RowDescent.down_eq_thDn f t (hR.row t) n h ⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, hMem⟩
    (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F) (_root_.GlobalTheory.RowDescent.apex_eq_toMap_geometricDatum W t F)
  have hC : (_root_.GlobalTheory.Fam.pk_z W).IsChain := RealDat.chain_of_weak W.Q.charW.base.chain hP.ex
  have e2 : _root_.GlobalTheory.MiTop.rowFormOfTuple W t F = PiTensorProduct.lift ((_root_.GlobalTheory.Fam.pk_z W).HE.e ((_root_.GlobalTheory.Fam.pk_z W).Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))) := rfl
  have e3 := congrArg PiTensorProduct.lift (hC.Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))
  have hFixed := GlobalTheory.GoodFix.good_fix (W.P.A3.A.fam.R t)
    (W.P.A3.A.fam.lvl W.Q.F.P1 W.Q.F.ψ1) hs.ok2.irr F
  have e4 := _root_.GlobalTheory.RowDescent.piTensorProduct_lift_postOn_eq_of_fixed W _ (fun v =>
    GlobalTheory.GoodFix.goodProjector_fixes_compositeThetaLift_of_fixed
      GlobalTheory.RapidDecay.cuspRapidDecay (_root_.GlobalTheory.Fam.pk_z W)
      hChar.lev hChar.models hChar.chain hChar.grp.red_R t _ hFixed v)
  exact e1.trans (e4.symm.trans (e3.symm.trans e2.symm))
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricDatumOfFamilyStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkDown_of_famCh : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkDescends f := by
  first | exact @_root_.GlobalTheory.MiTop.linkDown_of_ok | exact _root_.GlobalTheory.MiTop.linkDown_of_ok | (intros; apply _root_.GlobalTheory.MiTop.linkDown_of_ok <;> assumption)
end
end
end
