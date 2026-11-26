module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMap

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
namespace Formalism.L2.Rows
open Formalism.L2.DIV Formalism.L2.Indef
section Joint
variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 I0 Ty T : Type}
  (A3 : FamIn3 D.what₂.LL Gp Pl0 I0 Ty T D.R.m)
end Joint
section Bundle
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl Kc Y cX}
open Classical in
structure RowSideDeterminedAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
  ambS : ∃ JA : AmbIds D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup,
    AmbTie D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup P.I.jA JA
  faces : ∃ (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs, SPer (Dcf Zs)),
    Dcf P.Zs = P.Dc ∧ HEq (Spf P.Zs) P.Sp
  gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam
end Bundle
end Formalism.L2.Rows
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
def lamOfCol_alt {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) :
    ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i) :=
  fun u i τ =>
    cast (congrArg (fun R : Ranks => DomWeight (R.N i)) K.kerTie.2.1)
      (K.c.W.lamTrue (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u)) i
        (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ)))
open Classical in
def columnAddCharacter {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : ∀ PP : Pl K.X.E, AddChar (kP PP) D.what₂.LL :=
  fun PP => if h : PP ∈ K.c.Pr.vGs then K.c.Ch.psi0 ⟨PP, h⟩ else 1
open Classical in
structure ColumnCharactersCompatible {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : Prop where
  grpTie : HEq P.grp (inferInstance : Group (Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r))
  psTie : HEq P.Ps K.c.Lv.grp ∧ HEq P.ψs K.c.Lv.chr
  pointCharacterEq : HEq P.P0 (P0 K.c.Pr.vGs K.c.Rk.r (_root_.Formalism.L2.DIV.columnAddCharacter K)).H ∧ HEq P.ψ0 (P0 K.c.Pr.vGs K.c.Rk.r (_root_.Formalism.L2.DIV.columnAddCharacter K)).chi
  wOk : K.c.W.Ok
  chOk : K.c.Ch.Ok
  hcTie : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    HEq (K.c.W.hc (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u))
      (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ))) (D.hcW u τ)
  wtTie : ∃ (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ),
    Formalism.L2.Ker.KerEntTied.WtTie T.ker (_root_.Formalism.L2.DIV.lamOfCol_alt K) sh n
  xgTie : ∀ χ : Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r → D.what₂.LL,
    χ ∈ K.c.Xg ↔ (fun g => χ (cast K.gEq (P.I.eG.symm g))) ∈ Formalism.L2.Col.XgE K.c.Am.σ₀ D.ntypes.e0
  qNF : ∀ (t : P.A3.fam3.base3.Tup) (j : ℕ) (b : (K.c.Li t).β j)
      (v : ↥(Formalism.L2.Col.uSG K.c.Pr.vGs (Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL)))),
      v.1 ∉ K.c.Pr.vGs → 1 ≤ j → j + 2 ≤ K.c.Rk.m →
      ∃ (nn : Fin (Formalism.L2.Col.cOf K.c.Rk j) → ℤ) (z : Fin (K.c.Rk.N j) → K.X.E),
        (∀ i, -(j : ℤ) ≤ nn i ∧ nn i ≤ 0) ∧
        (fun l : Fin (K.c.Rk.N j + Formalism.L2.Col.cOf K.c.Rk j) => if h : l.1 < K.c.Rk.N j then z ⟨l.1, h⟩ else 0) ∈
          Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1 ∧
        (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
                  (((K.c.Li t).h j b v).toLinearMap.restrictScalars (𝓞 K.X.E)) =
          (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
            ((Matrix.toLin' (nfMat (K.c.Rk.N j) (Formalism.L2.Col.cOf K.c.Rk j) ((Formalism.L2.Col.qOf v.1 : ℕ) : K.X.E) nn z)).restrictScalars
              (𝓞 K.X.E))
  columnEvaluationOk : ∃ hM : (Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).Ok, ∀ u : D.what₂.Word,
    ∃ ι : (D.mem u).P.Mt ≃ₗ[ℂ] (Fin ((Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).hDim hM) → ℂ),
      (∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (y : Fin (rDim D P.A3.A P.Ps P.ψs t) → D.what₂.LL),
        ∃ (F' : (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun)
          (hm : F'.1 ∈ (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun),
          HEq ((Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).res
              (Formalism.L2.Col.mtildeKOk K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.hX) F')
            ((P.A3.A.fam.R t).S.basis.equivFun.symm
              (((P.A3.A.fam.R t).S.cutE (P.A3.A.fam.R t).r (lvlIdem (P.A3.A.fam.lvl P.Ps P.ψs).P
                (P.A3.A.fam.lvl P.Ps P.ψs).ψ)).mulVec y)) ∧
          ι ((D.eMt u).symm (ht ▸ P.I.jA t y)) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
        ∃ hm : ((K.c.ev P.Zs t F : Formalism.L2.Col.V0X K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Xg K.c.Lv) :
            (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun).1 ∈
            (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun,
          ι ((D.eMt u).symm (ht ▸ P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨_, hm⟩
end Formalism.L2.DIV
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.LabTameOfLabTie
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

namespace GlobalTheory.LabLaws

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem labTameS_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : UpperTheory.GalS.LabTameS N A := by
  refine ⟨fun k v a ha σ hσ hw => ?_, fun k v a ha hs hb => ?_⟩
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim] at ha
    rw [T.inePol _ a σ hσ, ← T.dim]
    exact WD.inePol_wild_of_natDegree_lab ha hw
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim] at ha
    rw [(hT k v).2.2] at hs
    refine (UpperTheory.GalS.nc_iff T a).2 (UpperTheory.GalS.SepW.ncW ⟨WD.tame_of_natDegree_lab ha, _, (hT k v).2.1.1, ?_⟩
      (UpperTheory.GalS.thr_split (H.g_prime k) (A.plGw_over k v) (N.g_split k) (by rwa [T.dim])))
    rw [WD.inePol_eq_of_natDegree_lab _ _ _ ha]
    exact GlobalTheory.GoodRowMono.separable_prod_teich _ (hT k v).1 hs

end GlobalTheory.LabLaws
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TieLabAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    Formalism.MainNotions.SumRepresentations.tieLab D ∧ _root_.UpperTheory.GalS.LabTameS D.nd D.naut ∧ IotaRed D ∧ GlobalTheory.RowCopy.RbarTie D := by
  intro hL D P
  let γ : Fin 2 → PlE D.host → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om := fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1)
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  have hT : GlobalTheory.LabLaws.LabTie P.T D.ntypes.teichC γ := by
    intro k v
    rw [hγ k v]
    exact ⟨D.ntypes.teichC_inj k, D.ntypes.tg_gen k v, P.lab k v⟩
  refine ⟨GlobalTheory.LabLaws.tieLab_of_labTie hT, _root_.GlobalTheory.LabLaws.labTameS_of_labTie hT, ?_, ⟨P.ty.rbarSS, P.ty.rbar⟩⟩
  intro i
  refine ⟨P.ty.plB (D.nd.w i), P.ty.plκ (D.nd.w i), fun y => P.ty.plB_loc i y, fun k v x => ?_⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hm := GlobalTheory.ParRay.mem_of_monoidHom (P.ty.plB (D.nd.w i)) (D.ntypes.teichC k) x
  refine ⟨hm, ?_⟩
  rw [P.ty.plB_iota i k v x]
  unfold redThrough
  exact dif_pos hm
end GlobalTheory.TieLabAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPinMin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure RowPinMinAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
end Formalism.L2.Rows
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisPreconditions
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain
structure GaloisPreconditions (D : D7) (C : NChoice D) : Prop where
  what₂ : _root_.GlobalTheory.NRows.PointConditions' D
  adm : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D
  Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
  z : SumRepresentations.ConclusionZ D
  rhoBar : ResidualIrreducibleRankR D
  g3p : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D
end UpperTheory.GalC
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerMapTieTw
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.Mem.Col2.LowerTie
theorem lowerMap_tieTw_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSKAlt ex) (he : ex.tw = I.tw l l0 Z), I.StdC l Z T.cols → I.StdTw l Z l0 (he ▸ T.tw) → ∀ u a (ha : a ≠ (I.rec7 l Z).what₂.mu0) (h1 : 1 ≤ B.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u a ha h1 :=
  fun I hO hP l Z l0 _ _ _ _ _ _ _ _ T he hC hTw u a ha h1 => lowerMap_tw_gen I hO hP l Z l0 T.tw he hC hTw u a ha h1
end GlobalTheory.Mem.Col2.LowerTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenActionAtGoodPoint
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenActionAtGoodPoint
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.PassOp
open Formalism.MainNotions.N.PlaceLabelTeichmuller
section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
end Tensor
local instance  (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
local instance  (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
theorem exists_isBCV_twistIso_append_mu_of_mem_Z (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i) (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) :
    ∃ Sig, IsBCV D.nd D.naut i PI
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  obtain ⟨P0, hP0, Pa0, hB0, hm⟩ := (D.Z_tie i x).1 hx
  obtain ⟨Pa, hB⟩ := h1 i PI
  have hperm : Pa0.Perm Pa := ((h41 i).2.1 P0 PI (by rw [hP0]; exact Option.some_ne_none x)
    (hP0.trans hPI.symm)).1 Pa0 Pa hB0 hB
  have hm' := hperm.subset hm
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm'
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  have hperm2 : (l₁ ++ m :: l₂).Perm ((l₁ ++ l₂) ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hB' := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm2 hB
  have hL : ∀ p ∈ l₁ ++ l₂, 1 ≤ p.a := fun p hp => (hB.1 p (by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  refine ⟨twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT, ?_⟩
  have e : twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
      D.naut.etaTinv = (l₁ ++ l₂) ++ [m] := by
    rw [show twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT) D.naut.etaTinv ++
          twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
      twistIso_eta D h0.1 h5.1 _ hL]
    rfl
  rw [e]
  exact hB'
theorem onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem (D : D7) (Q : PairedCharacterCondition.Pend D) (hSer : GlobalTheory.TypeLeaf.SerLoc D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i)
    (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) :
    (x ∈ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
    (x ∉ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := by
  have hon : ∀ σ' : D.ntypes.Par, F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' →
      (D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
      (¬ D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := fun σ' hF' =>
    idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => hSer i σ' k v f F hF' hf
  have hmem : ∀ Sig (σ' : D.ntypes.Par), (∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w) →
      IsBCV D.nd D.naut i PI (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) →
      F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
    intro Sig σ' hσ hB
    have hle : D.naut.typeV i PI ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
      rw [D.mtpar_tie i σ']
      exact le_iSup₂_of_le PI ⟨Sig, fun w => (hσ w).symm, hB⟩ le_rfl
    exact hle hF
  constructor
  · intro hg
    obtain ⟨-, Sig, ⟨P2, hP2, hB2⟩, hgs⟩ := (D.Zgood_tie i x).1 hg
    obtain ⟨Pa, hB⟩ := h1 i PI
    have hperm := ((h41 i).2.1 P2 PI (by rw [hP2]; exact Option.some_ne_none x)
      (hP2.trans hPI.symm)).1 _ Pa hB2 hB
    have hBPI := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨P2, hP2, hB2⟩
    exact (hon σ' (hmem Sig σ' hσ hBPI)).1 ((goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).2 hgs)
  · intro hg
    obtain ⟨Sig, hB⟩ := _root_.GlobalTheory.PassOp.exists_isBCV_twistIso_append_mu_of_mem_Z D h0 h1 h5 h41 i x hx PI hPI
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨PI, hPI, hB⟩
    refine (hon σ' (hmem Sig σ' hσ hB)).2 fun hgp => hg ?_
    rw [D.Zgood_tie i x]
    exact ⟨(D.Z_tie i x).1 hx, Sig, ⟨PI, hPI, hB⟩, (goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).1 hgp⟩
theorem main_alt_alt : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D →
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  intro D Q hEig hCen hSer h41 _ h0 h1 h5 i _ _
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  have hact : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
    intro F
    rw [hz]
    unfold NTypes.onMt
    rw [dite_eq_left (Subalgebra.smul_mem _ hcen _), dite_eq_left hcen, ← LinearMap.smul_apply, ← map_smul]
    rfl
  refine ⟨Q.zO i z, Q.zO_comm i z, ?_, ?_⟩
  · intro x hx u hu
    have hZ : x ∈ D.nd.Z i := (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
    have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
      rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hZ PI hPI F hF).1 hx, map_natCast]) u hu
    rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
  · intro x hx hxg u hu
    have := hEig i z x 0 (fun PI hPI F hF => by
      rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg, smul_zero, map_zero, zero_smul]) u hu
    rw [this, zero_smul]
end GlobalTheory.PassOp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenActionAtGoodPointStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutingEndomorphismCondition_of_serLoc : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  first | exact @_root_.GlobalTheory.PassOp.main_alt_alt | exact _root_.GlobalTheory.PassOp.main_alt_alt | (intros; apply _root_.GlobalTheory.PassOp.main_alt_alt <;> assumption)
end
end
end
