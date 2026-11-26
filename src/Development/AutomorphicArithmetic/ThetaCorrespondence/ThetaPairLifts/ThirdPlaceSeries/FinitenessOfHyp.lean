module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesAtOfExpRelation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigHkDatBackStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExists

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlocksUniqueOfCgTrue
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlocksUnique
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspFam
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRep
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC _root_.Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne in
theorem exists_rep_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) (π : CG E a) (hc : π.IsCsd) (s : ℝ)
    (hr : ∀ τ, (π.infChar τ).Nodup ∧ ∀ z ∈ π.infChar τ, ∃ m : ℤ, z + (s : ℂ) = (m : ℂ) + ((a : ℂ) - 1) / 2) :
    ∃ r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : Formalism.ConjugateSelfDual.IsPlaceOver A w),
        UpperTheory.GalS.Aw (wdOf h hl ι r) (((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpTw s).lpTw ((1 - (a : ℝ)) / 2)) := by
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hr' : (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [((ParLaws.hasInfChar_infChar π τ).twist _).infChar_eq, (InfType.expo_of_infType E _).2.1 s hν τ]
    refine ⟨(hr τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact (hr τ).2 y hy
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι a ha _ _ hr' (isPolarized_twist_absPow hc s)
  refine ⟨r, Units.continuous_val.comp H.cont, fun w hl A h => ?_⟩
  have k := H.aw_locPar hL hF hl h
  have e := _root_.GlobalTheory.HeightCounting.Blocks.local_parameter_twist_abs_pow hL hF (CG.mk π) hν h
  exact (congrArg (fun x : WD h => UpperTheory.GalS.Aw (wdOf h hl ι r) (x.lpTw ((1 - (a : ℝ)) / 2))) e).mp k
end Polar
section True
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
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
include hF C in
theorem cuspFam_alt_alt (hG : _root_.UpperTheory.GalS.CuspUAlt) {l : ℕ} [hp : Fact l.Prime] (ι : Qbar l ≃+* ℂ) :
    CuspFam D.naut ι := by
  intro a ha π hc s hs
  have := host_isCMField D.host
  obtain ⟨r, h1, h3⟩ := _root_.GlobalTheory.HeightCounting.Blocks.exists_rep_alt_alt hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) s fun τ => by
    have := hs τ
    rwa [C.inf] at this
  have hfin : ∀ᶠ w : PlE D.host in cofinite, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by simpa using hp.out.ne_zero
    have hf : {v : PlE D.host | ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}.Finite :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
    exact hf.eventually_cofinite_notMem
  refine ⟨fun z σ => (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.eval z, fun z => ?_, ?_⟩
  · simp only [Matrix.eval_charpoly]
    exact (continuous_const.sub h1).matrix_det
  · filter_upwards [hfin, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ z
    have hu' := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
    have e : T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
      have hu2 := (T.unr w _).1 hu'
      rw [← D.naut.lpTw_add, T.tw, T.tw, C.loc] at hu2 ⊢
      exact ((h3 w hl _ _).eq_unr hu2).symm
    rw [galPol, T.frobEig w _ hu', e, ← frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ]
    exact (eval_map_apply ι.toRingHom _).symm
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
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
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions GlobalTheory.CuspRep Blocks
theorem CGTrueT.blocksUnique (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hJ : GlobalTheory.Published.JacquetShalikaRigidity)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) :
    BlocksUnique D := by
  intro Sig Sig' h _ _ e
  have := host_isCMField D.host
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  have h1 := fun p hp => h p (List.mem_append_left Sig' hp)
  have h2 := fun p hp => h p (List.mem_append_right Sig hp)
  exact Multiset.coe_eq_coe.2 ((perm_of_split hC (GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hJ (_root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF C))
    (_root_.GlobalTheory.HeightCounting.Blocks.cuspFam_alt_alt hF C hG (l := 2) ι) (fun p hp => ⟨(h1 p hp).1, (h1 p hp).2.1⟩) (fun p hp => ⟨(h2 p hp).1, (h2 p hp).2.1⟩)
    ⟨fun p hp => (h1 p hp).2.2.1, fun p hp => (h1 p hp).2.2.2⟩ ⟨fun p hp => (h2 p hp).2.2.1, fun p hp => (h2 p hp).2.2.2⟩
    (Filter.Eventually.of_forall e)).map _)
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
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions GlobalTheory.CuspRep Blocks
theorem blocksUnique_of_cgTrue_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL →
    _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.JacquetShalika →
    GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → BlocksUnique D :=
  fun hL hF hG _ hJ hC _ _ C => C.blocksUnique hL hF hG hJ.1 hC
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsAtStart
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkRowL
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkRowL
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open _root_.Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem hecke_expansion_heightData_of_levelC {x : St P}
    (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) :
    NExpHeckeRowX x.m.z.R x.m.z.cG l.rat.S l.b.YS
      (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l) fun _ => LinearMap.id :=
  hkRow_of_ad x.m.z.R x.m.z.cG l.rat.kKs l.rat.hk l.b.YS
    (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l) l.rat.In.Sb l.b.fi l.b.Sb_le l.rat.rat.hecke

theorem hecke_expansion_datL_of_levelC {x : St P} (L : LocAll (lay0 (Dof x)))
    (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) :
    NExpHeckeRowX (datL x L).R (datL x L).cG (SL L l.rat)
      (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l)
      (_root_.GlobalTheory.HeightCounting.Fin3.localHeckeHeightData L l) fun _ => LinearMap.id := by
  constructor
  intro i k Q hsplit hoff houtside htwo hk α R hα hR y hy
  with_unfolding_all
    exact (hecke_expansion_heightData_of_levelC l).tie
      i k Q hsplit hoff houtside htwo hk α R hα hR y hy
end GlobalTheory.HeightCounting.Fin3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkRowLStatement
alias GlobalTheory.T.hecke_expansion_local_of_levelC :=
  GlobalTheory.HeightCounting.Fin3.hecke_expansion_datL_of_levelC
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GrpTieOfLCStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.Fin3

theorem grpTie_of_LC_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) := by
  intro hL K B f T w P x l
  have hc := GlobalTheory.Mem.R3.pins_card_index_ranks _ _ _ _ _ _ _ _ _ _ x.m.z.pins
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  obtain ⟨_, _, _, he0, _, _⟩ := x.m.z.pins.keep.grp
  refine ⟨hc.1, he0, ?_, ?_, hc.2.1, x.m.z.pins.keep.psi.lvl⟩
  · intro g
    rw [hU]
    exact l.rat.rat.lvl g
  · intro u hu i b
    have hu' : (x.m.z.R.eG.trans x.m.z.cG) u ∈ Formalism.IndefR.NX.U (Dof x).nd := by
      simpa only [hU] using hu
    refine ⟨psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩, l.rat.rat.psi u hu', ?_⟩
    exact l.b.Bs.psiU i b _ hu hu'

end GlobalTheory.HeightCounting.Fin3

theorem _root_.GlobalTheory.T.grpTie_of_levelC : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) :=
  @GlobalTheory.HeightCounting.Fin3.grpTie_of_LC_alt
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtAdL
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtAdL
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
theorem exists_mtAd_psi_vector_of_yRel {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
    {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    ∃ ad : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l), ad.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
  refine ⟨{ PV := _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l
            std := (by with_unfolding_all exact (l.mt.ad.std :))
            eW := (by with_unfolding_all exact (l.mt.ad.eW :))
            read := fun μ h i y g => ?_
            rat := (by with_unfolding_all exact (l.mt.ad.rat :))
            wt := (by with_unfolding_all exact (l.mt.ad.wt :))
            id := (by with_unfolding_all exact (l.mt.ad.id :)) }, rfl⟩
  have h1 := l.mt.ad.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))
  have h2 := hY.jMt μ h i y
  with_unfolding_all
    exact h1.trans (congrFun (eq_of_heq h2) _).symm
end GlobalTheory.HeightCounting.Fin3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtAdLStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel :
    ∀ {hL : UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre}
      {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P}
      (L : LocAll (lay0 (Dof x))) (l : StrictHenselianAcyclicLevel hL x)
      {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0),
      YRel L Y → ∃ ad : MtAd Y (localMultiplicityFamily L l), ad.PV = psiVectorLocal L l :=
  @GlobalTheory.HeightCounting.Fin3.exists_mtAd_psi_vector_of_yRel
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmtThetaL
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmtThetaL
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Fin3
theorem emtTheta_L_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0)
    (hY : YRel L Y) : EMtTheta Y (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) := by
  intro v i hv y hy n a f h
  with_unfolding_all
    have hOriginal := HEq.trans (heq_of_eq h) (hY.eW i _)
    exact (l.c.th v i hv y hy n a f (eq_of_heq hOriginal) :)
end GlobalTheory.HeightCounting.Fin3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmtThetaLStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.emtTheta_of_yRel
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre}
    {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P}
    (L : LocAll (lay0 (Dof x))) (l : StrictHenselianAcyclicLevel hL x)
    {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) :
    YRel L Y → EMtTheta Y
      (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l)
      (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) :=
  _root_.GlobalTheory.HeightCounting.Fin3.emtTheta_L_alt L l Y
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieOfTrue
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.NchAt
set_option maxHeartbeats 4000000 in
theorem tie_of_true_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'} {tp' : TupTied D' cf' C'}
    (b : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') : NChTie D' C' ∧ PsiChoiceCompatible D' cf' C' tp' := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := b
  subst eq
  cases pack
  refine ⟨⟨Sp.twOf_eq, Sp.twSide_eq, fun a => ?_, ?_, ch.nct.embedding_baseField_condition⟩, ch.psi⟩
  · exact (Sp.Q_eq _ _ a (((L.X.nd.locs_mem _ _ a).2 ⟨rfl, rfl⟩))).trans (Sp.Qc_eq _ _)
  · obtain ⟨ψ0, hc, hw, -⟩ := ch.nct.psi_eq
    exact ⟨ψ0, hc, hw, fun a g => Sp.psi_eq a g _ (hw _ g)⟩
end GlobalTheory.HeightCounting.NchAt
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
theorem mtInput_of_levelC : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
  show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
  rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt
variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))
def nTrueAtWeight : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
  { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row
    low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs
    M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := _root_.GlobalTheory.HeightCounting.Fin3.mtInput_of_levelC l, big := big, L := L, Sp := Sp, Au := Au, ss := ss
    eq := rfl, pack := rfl }
variable (L) in
structure AllLevelsData : Type 1 where
  a : _root_.GlobalTheory.HeightCounting.NAllCAlt (withLoc L) (chL L l.c.ch)
  chr : (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L l.c.ch)) = ⟨cfL L (cfOf x), tpL L l.c.tp⟩
  jE : a.gal.fr.jE = l.a.jE
  mt : a.gal.mt = mtL L l.mt.M
  exp : ExpRel L l.b.Bs.exp a.exp
  chrN : NCharTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  chrGal : NGalChrTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  loc : ∀ F : Formalism.L2.RowFrame (withLoc L), F.rep = repOf x.r.Y → _root_.Formalism.L2.RowLocTiedAlt (withLoc L) a.gal.lp F
variable (al : _root_.GlobalTheory.HeightCounting.Fin3.AllLevelsData l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))
theorem pq_weight_eq (i j b k Q ψ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (hadm : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) :
    plsOf al.a.exp i j b k Q ψ h1 h2 hadm = (qpOf (Dof x) l.Pq Q, qpOf (Dof x) l.Pq ((Dof x).ntw.pD i)) :=
  (al.exp.pl i j b k Q ψ h1 h2 hadm).trans (Prod.ext (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).1 (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).2)
def weightedAtData : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) where
  nt := _root_.GlobalTheory.HeightCounting.Fin3.nTrueAtWeight l Sp Au ss
  all := al.a
  chr_eq := al.chr
  host := ⟨(by with_unfolding_all exact (l.a.host.fr :)), (by with_unfolding_all exact (l.a.host.jLL :)), (by with_unfolding_all exact (l.a.host.embLL :))⟩
  frameN := by
    intro y
    with_unfolding_all exact (RingHom.congr_fun al.jE y).trans (l.a.frame y)
  chrN := al.chrN
  chrGal := al.chrGal
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  pq := fun i j b k Q ψ h1 h2 hadm => ⟨(by with_unfolding_all exact ((congrArg Prod.fst (_root_.GlobalTheory.HeightCounting.Fin3.pq_weight_eq l al i j b k Q ψ h1 h2 hadm)) :)),
    (by with_unfolding_all exact ((congrArg Prod.snd (_root_.GlobalTheory.HeightCounting.Fin3.pq_weight_eq l al i j b k Q ψ h1 h2 hadm)) :))⟩
  jE_eq := (by with_unfolding_all exact ((heq_of_eq al.jE.symm) :))
  mt_eq := (by with_unfolding_all exact ((heq_of_eq al.mt.symm) :))
  Pq_eq := (by with_unfolding_all exact ((HEq.refl l.Pq) :))
  low := (by with_unfolding_all exact ((low_ok (Dof x)) :))
  split := hLg.2.1
  ratIn := l.rat.In
  ratIn_hL := rfl
  ratIn_eig := rfl
  ratIn_θ := rfl
  depth := l.a.depth
def localAtData : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (DL x L) (cfD x L) (characterChoiceLocal L l) (localCharacterTupleAgreement L l) := by
  let a := weightedAtData l Sp Au ss al hLg
  -- Keep the local indices on the constructors so that the row data still reduce fieldwise.
  refine {
    nt := ?_, all := ?_, chr_eq := ?_, host := ?_, frameN := ?_, chrN := ?_
    chrGal := ?_, Pq := ?_, Pq_over := ?_, pq := ?_, jE_eq := ?_, mt_eq := ?_
    Pq_eq := ?_, low := ?_, split := ?_, ratIn := ?_, ratIn_hL := ?_, ratIn_eig := ?_
    ratIn_θ := ?_, depth := ?_ }
  · refine { toNBuilt := { a.nt.toNBuilt with eq := DL_eq x L }, pack := ?_ }
    with_unfolding_all rfl
  · with_unfolding_all exact a.all
  · with_unfolding_all exact a.chr_eq
  · with_unfolding_all exact a.host
  · intro y
    with_unfolding_all exact a.frameN y
  · with_unfolding_all exact a.chrN
  · with_unfolding_all exact a.chrGal
  · with_unfolding_all exact a.Pq
  · intro v
    with_unfolding_all exact a.Pq_over v
  · intro i j b k Q ψ h1 h2 hadm
    with_unfolding_all exact a.pq i j b k Q ψ h1 h2 hadm
  · with_unfolding_all exact a.jE_eq
  · with_unfolding_all exact a.mt_eq
  · with_unfolding_all exact a.Pq_eq
  · with_unfolding_all exact a.low
  · with_unfolding_all exact a.split
  · exact a.ratIn
  · exact a.ratIn_hL
  · exact a.ratIn_eig
  · exact a.ratIn_θ
  · exact a.depth
include l in
variable (L) in
theorem grpTie_famR : Formalism.L2.DIV.GrpTie (DL x L) (famR (w.st (oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) (datL x L).Xg (datL x L).tr).A
    (datL x L).F.P0 (datL x L).F.ψ0 (datL x L).F.P1 (datL x L).F.ψ1 ((datL x L).R.eG.trans (datL x L).cG) :=
  ⟨(by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).card :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).e0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).lvl0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).psi0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).idxSharp :)),
    (datL x L).pins.keep.psi.lvl⟩
variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)
def normalizedRowDatum : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := DL x L) (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg) (datL x L).R (datL x L).F (datL x L).cG Y where
  kKs := kKsL L l.rat
  hk := hkL L l.rat
  nexp := _root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l
  hecke := _root_.GlobalTheory.HeightCounting.Fin3.localHeckeHeightData L l
  grp := _root_.GlobalTheory.HeightCounting.Fin3.grpTie_famR l L
  rowLoc := by
    let F : Formalism.L2.RowFrame (withLoc L) :=
      ⟨(frameY Y).rep, (frameY Y).inj⟩
    have hF : F.rep = repOf x.r.Y := by
      with_unfolding_all exact eq_of_heq hY.rep
    exact ⟨by with_unfolding_all exact (al.loc F hF).sat⟩
  S_eq := (by with_unfolding_all exact ((SL_heq L l.rat) :))
  hL_eq := (by with_unfolding_all exact ((HEq.refl l.rat.In.hL) :))
  rep_eq := (by with_unfolding_all exact (hY.rep.symm :))
theorem nonempty_nMore_of_xdAll {xd : ThData (Dof x)} (hxd : XdAll xd) : Nonempty (_root_.GlobalTheory.HeightCounting.RealExpansionExtraData (_root_.GlobalTheory.HeightCounting.Fin3.normalizedRowDatum l Sp Au ss al hLg Y hY) (datL x L).geo (xdD L xd)) := by
  have e : (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).all.gal.mt = _root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l := (by with_unfolding_all exact (al.mt :))
  have H : ∃ ad' : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).all.gal.mt, ad'.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
    rw [e]
    exact _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel (x := x) L l Y hY
  obtain ⟨ad', had'⟩ := H
  have hSer : Nonempty (SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l)
      (datL x L).geo.v₀ (expD L al.a.exp) (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l)
      (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l)) :=
    _root_.GlobalTheory.T.series_at_local_of_exp_relation (x := x) L l al.a.exp al.exp
  obtain ⟨ser⟩ := hSer
  have ser' : SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L al.a.exp) ad'.PV (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l) := had'.symm ▸ ser
  exact ⟨{ ad := ad'
           fi := _root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal_fi_e_heq L l
           hecke := _root_.GlobalTheory.T.hecke_expansion_local_of_levelC L l
           cHk := (by with_unfolding_all exact ((fun i b Q => (⟨l.b.Bs.cHk i b Q, pow_one _⟩ : ∃ u : ((Dof x).ntw.O i)ˣ, (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).cHk i b 1 Q =
             algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) u)) :))
           eig := ⟨_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l, _root_.GlobalTheory.HeightCounting.Fin3.localEigenvalueDegree L l, (by with_unfolding_all exact (l.b.Sb_le :)), (by with_unfolding_all exact ((HEq.refl l.rat.In.eig) :)), _root_.GlobalTheory.T.eigAd_of_yRel_at_level_c L l Y hY⟩
           ser := (by with_unfolding_all exact (ser' :))
           tau := (by with_unfolding_all exact ((al.exp.tau l.b.tau) :))
           geo := _root_.GlobalTheory.HeightCounting.Fin3.thetaTie_yStructureLocal_nonempty L l
           ok := _root_.GlobalTheory.HeightCounting.Fin3.twist_ok_local L l
           th := _root_.GlobalTheory.T.emtTheta_of_yRel L l Y hY
           xd := xdD_all L hxd
           large := (by with_unfolding_all exact (hLg :))
           labc := (by with_unfolding_all exact (l.a.labc :))
           zeta := (by with_unfolding_all exact (l.a.zeta :))
           pht := (by with_unfolding_all exact ((⟨l.a.fr, l.a.fr_jE, l.a.pht⟩ : ∃ fr : Formalism.L2.OmFrame (Dof x), fr.jE = l.a.jE ∧ PhtOn l.a.A.wd fr fun _ _ _ _ => True) :)) }⟩
def localCharacterChoiceTwist : NchT w (oL x L).Z P.Wt (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) where
  tp := _root_.GlobalTheory.HeightCounting.Fin3.localCharacterTupleAgreement L l
  xi := (by with_unfolding_all exact (l.c.xi_eq :))
  psi := (by with_unfolding_all exact (l.c.psi_eq :))
  tie := (_root_.GlobalTheory.HeightCounting.NchAt.tie_of_true_alt (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).nt).1
  Q := fun v hv => ⟨(by with_unfolding_all exact (((congrFun l.c.Q_eq v).trans (GlobalTheory.HeightCounting.Up.Model.qOf_on v hv)) :)),
    (by with_unfolding_all exact ((l.c.k_eq v ((GlobalTheory.HeightCounting.Up.Model.twisted_iff x v).2 hv)) :))⟩
  chrPsi := (_root_.GlobalTheory.HeightCounting.NchAt.tie_of_true_alt (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).nt).2
include hY in
theorem exists_core_and_listPin {xd : ThData (Dof x)} (hxd : XdAll xd) (t : RowsT K w (oL x L).Z P.Wt p0) (hz : HEq t.r.z (datL x L))
    (ht : HEq t.r.Y Y) : ∃ c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterChoiceTwist l Sp Au ss al hLg),
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w (oL x L).Z P.Wt p0 t (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterChoiceTwist l Sp Au ss al hLg) (xdD L xd) c) ∧
      ∀ cDep : ℝ, ListSt cDep x → ListPin (DL x L) t.r.z.R.toRealDat.toLevCh cDep K.s.b := by
  obtain ⟨hX, ⟨z, intersectionNumber_baseChange, Y', Zr, tix⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := t
  have e : z = datL x L := eq_of_heq hz
  subst e
  have e' : Y' = Y := eq_of_heq ht
  subst e'
  obtain ⟨mo⟩ := _root_.GlobalTheory.HeightCounting.Fin3.nonempty_nMore_of_xdAll l Sp Au ss al hLg Y' hY hxd
  exact ⟨⟨_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg, _root_.GlobalTheory.HeightCounting.Fin3.normalizedRowDatum l Sp Au ss al hLg Y' hY, (by with_unfolding_all exact (l.sel :))⟩, ⟨(mo, ⟨bkL L⟩)⟩, fun cDep h => GlobalTheory.T.toricCharacterGridList_kept_localizedStage x L cDep h⟩
omit l in
theorem exists_read_heq_of_eq {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} (e : z = z') {p : BaseLevelRowSide (w.D Z)}
    (Y₀ : Read z.R.toRealDat z.F.lv2 p) : ∃ Y₁ : Read z'.R.toRealDat z'.F.lv2 p, HEq Y₁ Y₀ := by
  subst e
  exact ⟨Y₀, HEq.rfl⟩
omit l in
theorem start_at_all_pre2 : StepW Start fun K _ _ _ w => ∀ P : Pre2 K w, RowsAt P :=
  Step.trans GlobalTheory.Mem.R3.Rw.St.exists_rowsT (Step.of_all fun _ _ _ _ _ _ _ H w hs P => H w ⟨hs.1, ⟨P⟩⟩ P)
end GlobalTheory.HeightCounting.Fin3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NAllCWithLoc
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NTiedLocTiedOfBuilt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting
theorem nTied_locTied_of_built_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.CgCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'),
    Nonempty (_root_.GlobalTheory.HeightCounting.NTiedGPlaceholder D') ∧ Nonempty (Formalism.L2.LocTied D') := by
  intro hL hcg D' b
  exact ⟨⟨⟨⟩⟩, locTied_any D'⟩
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalTiedWithLoc
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.FitGal
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem galTied_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.LpCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ g : _root_.Formalism.L2.NGalTiedAlt (withLoc b.L), g.fr.jE = b.jE ∧ g.mt = mtL b.L b.M ∧ g.tup = b.tp.tup ∧ Nonempty (NormalizedDataCompatibility (withLoc b.L)) ∧ Nonempty (NormalizedLocalCompatibility (withLoc b.L) (mtL b.L b.M)) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → _root_.Formalism.L2.RowLocTiedAlt (withLoc b.L) g.lp F := by
  intro hL hLp D' b fr hfr hpht hstar hexp hsplit hcheb
  obtain ⟨Hk, hHk⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch
    b.mt hstar hexp hsplit hcheb b.big b.L b.Sp b.Au
  let lp : LPTiedPlaceholder (withLoc b.L) := ⟨⟩
  let fr' : OmFrame (withLoc b.L) := { fr with }
  have au : _root_.Formalism.L2.AUTiedAlt (withLoc b.L) lp (mtL b.L b.M) Hk.av :=
    { Hk.au with
      emb := Hk.emb }
  let g : _root_.Formalism.L2.NGalTiedAlt (withLoc b.L) :=
    { fr := fr', lp := lp, mt := mtL b.L b.M, hecke := Hk.hecke, av := Hk.av, au := au
      rational := Hk.rational, tup := b.tp.tup, level := Hk.level }
  refine ⟨g, hfr, rfl, rfl, ⟨Hk.data⟩, ⟨Hk.cover⟩, ?_⟩
  intro F hF
  refine ⟨fun i σ v w hov Dv hα => ?_⟩
  · rw [hF] at hα ⊢
    obtain ⟨α, hS, he⟩ := b.row.2 σ v w hov Dv hα
    refine ⟨α, hS, ?_⟩
    show b.L.Y.satW i σ w = _
    rw [b.Au.satW i σ w]
    exact he
end GlobalTheory.FitGal
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwOpenExpRel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwOpenExpRel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.FitTwExp
set_option maxHeartbeats 8000000 in
theorem exists_twOpen_expRel_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  intro hL D' b hE hC
  obtain ⟨Tw⟩ := _root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt hE.star hE.int hE.split hC b.big b.L b.Sp b.Au
  refine ⟨{ Tw with exp := GlobalTheory.HeightCounting.FitTw.expL b.L b.Bs.exp, ch := GlobalTheory.HeightCounting.FitTw.chSideL b.Sp b.ch }, ?_⟩
  exact
    { tau := fun h => h
      pl := fun _ _ _ _ _ _ _ _ _ => rfl
      reads := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h }
end GlobalTheory.HeightCounting.FitTwExp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwOpenExpRelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twOpen_expRel_of_chebSplit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  first | exact @_root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt | exact _root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRhoTiedWithLoc
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.FitRho
open _root_.Formalism.L2.NR
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting.FitRho
open _root_.Formalism.L2.NR
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting.FitRho
open _root_.Formalism.L2.NR
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rhoS_withLoc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (hcheb : GlobalTheory.RowTie.ChebSplit b.D.nd) (hP : RowPar (withLoc b.L)) (hG : GalRepEx (withLoc b.L))
    (hC : ClassFieldHeckeAlgebraic (withLoc b.L)) (hη : EtaShiftInt (withLoc b.L)) (a : (withLoc b.L).nd.Loc)
    (s : (withLoc b.L).ntw.Sig ((withLoc b.L).ntw.twOf a))
    (hs : (withLoc b.L).ntw.side _ s = (withLoc b.L).ntw.twSide a) (hj : (withLoc b.L).ntw.jS _ s = (withLoc b.L).nd.j a) :
    ∃ (σ : (withLoc b.L).what₂.FT) (hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) σ ≠ ⊥)
      (hg : (withLoc b.L).nd.goodRow σ),
      ∀ (π : (withLoc b.L).naut.CG (withLoc b.L).R.r) (hS : rowSig (withLoc b.L) a σ = [⟨(withLoc b.L).R.r, π, 1⟩]),
        IsConjRep (Formalism.MainNotions.N.mapRep ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
            ((withLoc b.L).ntw.rhoS _ s))
          (rhoOfRow (withLoc b.L) hG hC hη a π (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).1
            (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).2) := by
  obtain ⟨hiso, hgood, hspec⟩ := b.Bs.rhoS (b.L.T.twOf a) s
  have hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) (b.Bs.rowS (b.L.T.twOf a) s) ≠ ⊥ := by
    rw [← hj]; exact hiso
  refine ⟨b.Bs.rowS (b.L.T.twOf a) s, hσ, hgood, fun π hS => ?_⟩
  obtain ⟨hc, hr⟩ := rowSig_csd_ralg (withLoc b.L) hP a _ hσ hgood π hS
  have hloc : ∀ w, IsSplitPl b.D.host w → b.D.naut.locG π w = b.A.row.locR (b.Bs.rowS (b.L.T.twOf a) s) w := by
    intro w hw
    have h1 := (rowSig_spec (withLoc b.L) hP a _ hσ).2.2 w hw
    rw [hS] at h1
    exact ((isoLoc_single (withLoc b.L) π w).symm.trans h1).trans (b.Au.locW a _ w)
  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a
  let φ0 : FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) →+* Qbar ((withLoc b.L).nd.l a) :=
    ((withLoc b.L).naut.iotaQ a).comp (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))
  have hφ0 : φ0.comp (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)))) =
      (Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a) := by
    ext y
    show (withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y)) =
      (withLoc b.L).naut.iotaQ a (algebraMap _ _ ((withLoc b.L).ntw.twist₂ a y))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
  have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
      ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
      (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
    fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
      (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
  let φ := (castQ hpq).symm.toRingHom.comp φ0
  let ι := (castQ hpq).trans ((withLoc b.L).naut.iotaQC a)
  have hφ : ∀ z : ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)], φ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)) =
      algebraMap ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] (Qbar ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))) (z : ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)]) := by
    intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  have hι : ∀ x : ↥b.D.LL0, ι (φ ((if (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a)
      else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x)) = embLL0 b.D x := by
    intro x
    have hs' : (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s = (withLoc b.L).ntw.twSide a := hs
    rw [hs']
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  have hR := hspec π hc hr hloc φ ι hφ hι
  have hR' : IsRepOf (withLoc b.L) ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)) ((castQ hpq).trans ((withLoc b.L).naut.iotaQC a))
      ((withLoc b.L).naut.tw π (withLoc b.L).naut.etaTinv) ((1 - ((withLoc b.L).R.nV : ℝ)) / 2)
      (Formalism.MainNotions.N.mapRep (castQ hpq).symm.toRingHom (Formalism.MainNotions.N.mapRep
        ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
        ((withLoc b.L).ntw.rhoS _ s))) := by
    rw [← hφ0, mapRep_mapRep]
    exact hR
  exact conj_of_isRepOf (withLoc b.L) ((withLoc b.L).naut.iotaQC a) _ _ hcheb _ _
    (isRepOf_cast (withLoc b.L) hpq _ _ _ _ hR') (rhoOfRow_isRepOf (withLoc b.L) hG hC hη a π _ _)
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem nRhoTied_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → TypesOpen (withLoc b.L) b.jE → NR.NRhoTied (withLoc b.L) := by
  intro hL D' b _ _ _ hcheb hT
  exact ⟨hT.rbarSS, hT.rbar, fun hP hG hC hη a s hs hj =>
    _root_.GlobalTheory.HeightCounting.FitRho.rhoS_withLoc_alt hL D' b hcheb hP hG hC hη a s hs hj⟩
end GlobalTheory.HeightCounting
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting.FitAll
theorem nAllC_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.LpCmpAlt hL → _root_.GlobalTheory.HeightCounting.CgCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → lowPr b.D ⊆ b.low → ∃ a : _root_.GlobalTheory.HeightCounting.NAllCAlt (withLoc b.L) (chL b.L b.C), (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc b.L), TupTied (withLoc b.L) c (chL b.L b.C)) = ⟨cfL b.L b.cf, tpL b.L b.tp⟩ ∧ a.gal.fr.jE = b.jE ∧ a.gal.mt = mtL b.L b.M ∧ ExpRel b.L b.Bs.exp a.exp ∧ Nonempty (NCharTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp)) ∧ NGalChrTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → _root_.Formalism.L2.RowLocTiedAlt (withLoc b.L) a.gal.lp F := by
  intro hL hLp hCg D' b fr hfr hpht hE hCh hlow
  obtain ⟨g, hgj, hgm, hgt, ⟨dat⟩, ⟨cov⟩, hrow⟩ :=
    _root_.GlobalTheory.FitGal.galTied_withLoc_alt hL hLp D' b fr hfr hpht hE.star hE.int hE.split hCh
  obtain ⟨⟨nt⟩, ⟨lt⟩⟩ := _root_.GlobalTheory.HeightCounting.nTied_locTied_of_built_alt hL hCg D' b
  obtain ⟨TO⟩ := _root_.GlobalTheory.HeightCounting.typesOpen_withLoc_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt
    hE.star hE.int hE.split hCh b.big b.L b.Sp b.Au b.ss
  have rho : NR.NRhoTied (withLoc b.L) := _root_.GlobalTheory.HeightCounting.nRhoTied_withLoc_alt hL D' b hE.star hE.int hE.split hCh TO
  obtain ⟨Tw, hX⟩ := _root_.GlobalTheory.T.exists_twOpen_expRel_of_chebSplit hL D' b hE hCh
  have ty : NormalizedTypesCompatibility (withLoc b.L) b.jE :=
    { eM := TO.par.eM, eM_K := TO.par.eM_K, tA := TO.grp.tA, tκ := TO.grp.tκ, teichC_def := TO.grp.teichC_def,
      iota_loc := fun i => ⟨TO.plB _, TO.plκ _, TO.plB_loc i, TO.plB_iota i⟩,
      ζ := TO.grp.ζ, ζ_gen := TO.grp.ζ_gen, O := TO.grp.O, eSer_def := TO.grp.eSer_def, kv := TO.grp.kv,
      tg_tame := TO.grp.tg_tame, O_equiv := TO.grp.O_equiv, O_tw := TO.grp.O_tw, eP := TO.par.eP,
      locPar_def := TO.par.locPar_def }
  let F0 : TwFrame (withLoc b.L) := ⟨Tw.twF.K0, Tw.twF.eO0, Tw.twF.j0, Tw.twF.Lw, Tw.twF.eO, Tw.twF.eOk, Tw.twF.iCq, Tw.twF.S0x⟩
  have hlow' : lowPr (withLoc b.L) ⊆ b.low := hlow
  have tw : NTwTied (withLoc b.L) F0 := by
    have T := Tw.tw
    have hN : Ideal.absNorm (withLoc b.L).host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (withLoc b.L).host.ccK_ne_bot
    have hd : (NumberField.discr (withLoc b.L).host.E).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero (withLoc b.L).host.E)
    exact ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos,
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hN])),
      fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])), fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])),
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hd]))⟩
  refine ⟨
    { gal := g, n := (b.eq ▸ nt), loc := (b.eq ▸ lt), data := dat, cover := (hgm ▸ cov), chiD := Tw.chiD, chi := Tw.chi,
      rho := rho, types := (hgj.symm ▸ ty), twF := F0, tw := tw, nct := Tw.ch.nct, exp := Tw.exp, choice := Tw.ch.choice,
      eMt_level := by rw [hgm]; exact Tw.ch.eMt_level,
      cf := cfL b.L b.cf, tp := tpL b.L b.tp, tupLink := hgt,
      eta_eq := Tw.eta_eq, ringSpec_normalisedCharacter_eq := Tw.ringSpec_normalisedCharacter_eq, del_eq := Tw.del_eq, psi_eq := Tw.psi_eq,
      plB := TO.plB, plκ := TO.plκ, plB_loc := TO.plB_loc, plB_iota := TO.plB_iota,
      etaT_link := Tw.etaT_link, muC_link := Tw.muC_link, iCq_embO := Tw.iCq_embO, embO_star := Tw.embO_star },
    rfl, hgj, hgm, hX, ⟨Tw.chrN⟩, Tw.chrGal, hrow⟩
end GlobalTheory.HeightCounting.FitAll
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
theorem builtEx_of_published_inputs' (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) : _root_.GlobalTheory.CoefDuty.AutomorphicSideExists l.a.A l.mt.M l.c.ch l.c.tp.tup := fun big =>
  _root_.GlobalTheory.T.side_rational_hecke_data_alt hP.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ l.b.Bs l.mt.M
    l.c.ch l.c.tp l.c.side (_root_.GlobalTheory.HeightCounting.Fin3.mtInput_of_levelC l) l.a.elem.star l.a.elem.int l.a.elem.split (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
    (fun v _ => by rw [l.c.psi_eq]; exact GlobalTheory.twDat_psi_valuesIn_LL B T P.coh v) l.a.omax
    (_root_.GlobalTheory.HeightCounting.blocksUnique_of_cgTrue_alt hL hP.what₂.fin hP.what₂.gal hP.what₂.art hP.what₂.js hP.what₂.cheb _ _ l.a.cg) big
variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))
include Au ss in
theorem nonempty_allL_of_archCmp (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hA : _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL) : Nonempty (_root_.GlobalTheory.HeightCounting.Fin3.AllLevelsData l L) := by
  obtain ⟨a, h1, h2, h3, h4, ⟨h5⟩, h6, h7⟩ := _root_.GlobalTheory.HeightCounting.FitAll.nAllC_withLoc_alt hL hA.lp hA.cg _ (_root_.GlobalTheory.HeightCounting.Fin3.nTrueAtWeight l Sp Au ss).toNBuilt l.a.fr l.a.fr_jE
    l.a.pht l.a.elem (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) Finset.subset_union_left
  exact ⟨⟨a, h1, h2, h3, h4, h5, h6, h7⟩⟩
omit l in
variable (x L) in
theorem exists_base_level_rXs_and_yRel (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hD : GlobalTheory.Published.DiscreteSeriesExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hR : RowsAt P)
    (he : ∀ j v, 1 ≤ j → j ≤ B.R.m → etaL x L j v = P.q.eta j v) :
    ∃ (p : BaseLevelRowSide (w.D (oL x L).Z)) (t : RowsT K w (oL x L).Z P.Wt p), Nonempty (RXs t) ∧
      ∃ Y₁ : YT x L p, YRel L Y₁ ∧ HEq t.r.z (datL x L) ∧ HEq t.r.Y Y₁ := by
  obtain ⟨m, hm, hc, hco⟩ := GlobalTheory.T.exists_movedData_state_localisations x L
  obtain ⟨s, r, hpin⟩ := GlobalTheory.T.exists_reading_of_rowLiftFamily_movedData B f T w P.Z₀ P.hX P.Wt P.z P.q (oL x L)
    (GlobalTheory.LinksInputs.inputs_of_hypotheses hW hD hP.hc hP.decay (w.D (oL x L).Z)) (fitsL L) m
  obtain ⟨t, rx, -, hz, hy, -⟩ := hR ⟨oL x L, fitsL L, x.G_eq, x.etaF, bkL L, m, hc, hco, s, r, hpin⟩ he
  obtain ⟨Y₁, h1⟩ := _root_.GlobalTheory.HeightCounting.Fin3.exists_read_heq_of_eq hm r.Y
  exact ⟨s.p0, t, rx, Y₁, GlobalTheory.T.normalisedReadings_related_localizedAdelicData x L m hm hco s r hpin Y₁ h1, hz.trans (heq_of_eq hm), hy.trans h1.symm⟩
theorem lv3_of_third_alt_alt (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hD : GlobalTheory.Published.DiscreteSeriesExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hA : _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL)
    (hR : RowsAt P)
    (hE : _root_.GlobalTheory.CoefDuty.AutomorphicSideExists l.a.A l.mt.M l.c.ch l.c.tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
      GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v)
    (hX : ∃ xd : ThData (Dof x), XdAll xd) (S : SExt) (Γ : GeoP) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL)
    (hN : ∀ Z p t nch n xd c, _root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z P.Wt p t nch n xd c →
      (∀ cDep : ℝ, ListSt cDep x → ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b) →
      Nonempty (N K B f T w Z P.Wt p t nch n xd c)) :
    ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch := by
  have hB := _root_.GlobalTheory.HeightCounting.Fin3.builtEx_of_published_inputs' l hP
  obtain ⟨big, hbig⟩ := hE hB
  obtain ⟨L, hL'⟩ := hB big
  obtain ⟨hLg, he⟩ := hbig L hL'
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hL'
  obtain ⟨al⟩ := _root_.GlobalTheory.HeightCounting.Fin3.nonempty_allL_of_archCmp l Sp Au ss hP hA
  obtain ⟨xd, hxd⟩ := hX
  obtain ⟨p, t, ⟨rx⟩, Y₁, hY₁, hz, ht⟩ := _root_.GlobalTheory.HeightCounting.Fin3.exists_base_level_rXs_and_yRel x L hW hD hP hR fun j v h1 h2 => he j v h1 h2 v HEq.rfl
  obtain ⟨c, ⟨ne⟩, hp⟩ := _root_.GlobalTheory.HeightCounting.Fin3.exists_core_and_listPin l Sp Au ss al hLg Y₁ hY₁ hxd t hz ht
  obtain ⟨nn⟩ := hN _ p t _ _ _ c ne hp
  have hg : GIs2 K w x.o.G := x.G_eq ▸ P.g
  exact ⟨(oL x L).Z,
    { g := hg, coh := P.coh, Wt := P.Wt, p0 := p, what₂ := t, rx := rx, nch := _root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l, n := _root_.GlobalTheory.HeightCounting.Fin3.localCharacterChoiceTwist l Sp Au ss al hLg, xd := xdD L xd
      chiT := fun k v => TypesTrue.chiT_gen (fitsL L).grp k v, nx := ⟨c, nn⟩ }, rfl, _root_.GlobalTheory.HeightCounting.Fin3.kept_characterChoiceLocal L l⟩
omit l in
theorem sFin_and_sFinl_of_theta_data_exists : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL → _root_.GlobalTheory.HeightCounting.Up.EtaStatement' hL → _root_.GlobalTheory.HeightCounting.Up.ThetaDataExists hL → _root_.GlobalTheory.HeightCounting.Up.FinitenessStatement hL ∧ ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep := by
  intro hW hD hP hL hA hE hX
  have h := _root_.GlobalTheory.HeightCounting.Fin3.start_at_all_pre2.and (StepW.and hE hX)
  refine ⟨h.trans (StepW.of_all ?_), fun cDep => h.trans (StepW.of_all ?_)⟩
  · intro K B f T w _ _ H P x l S Γ
    exact _root_.GlobalTheory.HeightCounting.Fin3.lv3_of_third_alt_alt l hW hD hP hA (H.1 P) (H.2.1 P x l) (H.2.2 P x ⟨l.toStrictHenselianAcyclic.toLI, l.b.toSeriesState⟩) S Γ (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL)
      fun _ _ _ _ _ _ _ a _ => ⟨a⟩
  · intro K B f T w _ _ H P x l S Γ hp
    exact _root_.GlobalTheory.HeightCounting.Fin3.lv3_of_third_alt_alt l hW hD hP hA (H.1 P) (H.2.1 P x l) (H.2.2 P x ⟨l.toStrictHenselianAcyclic.toLI, l.b.toSeriesState⟩) S Γ (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep)
      fun _ _ _ _ _ _ _ a b => ⟨(a, ⟨b cDep hp⟩)⟩
end GlobalTheory.HeightCounting.Fin3
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sFin_and_sFinl_of_archCmp_sEta_thetaData : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL → _root_.GlobalTheory.HeightCounting.Up.EtaStatement' hL → _root_.GlobalTheory.HeightCounting.Up.ThetaDataExists hL → _root_.GlobalTheory.HeightCounting.Up.FinitenessStatement hL ∧ ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep := by
  exact _root_.GlobalTheory.HeightCounting.Fin3.sFin_and_sFinl_of_theta_data_exists
end
end
