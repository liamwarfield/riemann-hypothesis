module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormRepX
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentFrameFixers
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section P

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def CtxP : Prop :=
  (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ IsRowReps D F0 what₂ ∧ Lat.PrimeHyp D u (Tu D u')

def FrGlobP : Prop := CtxP u u' F0 what₂ → FrGlob Zd u u' F0 what₂

def TauOneReduction : Prop := CtxP u u' F0 what₂ → Tau1 Zd u u' F0 what₂

def ExistP : Prop := CtxP u u' F0 what₂ → Exist Zd.M Zd.δ u u'

def SumFrP : Prop := CtxP u u' F0 what₂ → SumFr Zd.M Zd.δ u u' F0 what₂

variable {u u' F0 what₂}

theorem normRepExists_ctx (h : CtxP u u' F0 what₂) : PairVal.NormRepExists D u u' F0 what₂ := normRepExists_of (NormRepX.norm_representative_holds D u u' h.2.2) (Formalism.L2.SG.Closed.TermFun_holds D u u') h.2.1

theorem frCount_ctx (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : FrCount Zd.M Zd.δ u u' F0 what₂ := pcount_frCount Zd (normRepExists_ctx h) h.2.1 (hG h) hI (inOrbZ_holds Zd u u') (hτ h) hT

theorem partnerCount_ctx {θ0 : ∀ p, Option ((Zd.M p).Cls D.R.rS)}
    (hU : LocUnram Zd.M Zd.δ u u' θ0) (hR : ThRestricted Zd.M Zd.δ u u' F0 what₂ θ0)
    (hE : ExistP Zd u u' F0 what₂) (hS : SumFrP Zd u u' F0 what₂)
    (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : PartnerCount Zd.M Zd.δ u u' F0 what₂ := partnerCount_of hU hR h.2.1 (normRepExists_ctx h) eligRel_holds
    (restr_of Zd.3 h.2.1 (normRepExists_ctx h) eligRel_holds) (hE h) (hS h) (frCount_ctx Zd hG hI hτ hT h)

end P

end Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem partnerCount_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hP : Lat.PrimeHyp D u (Tu D u')) {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LsDatumB.LocUnram M δ u u' θ0) (hR : LsDatumB.ThRestricted M δ u u' F0 what₂ θ0)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩) :
    LsDatumB.PartnerCount M δ u u' F0 what₂ := PCount.partnerCount_ctx ⟨δ, M, hA⟩ hU hR hE hS hG hI hτ hT ⟨hc, hrows, hP⟩

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCut
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolCut

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.Coef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.IndexCocycleOrbits
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def HypE (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D) : Prop :=
  (∀ p, Agree δ M p) ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ IsRowReps D F0 what₂ ∧
    PrimeHyp D u (Tu D u') ∧ EligAt γ w ∧ PairVal.NormRep γ w F' L U

def stZSet (Z L : PairVal.MatR D) : Set (PairVal.GLR D) :=
  {a | ∃ a' : PairVal.GLR D, (a : PairVal.MatR D) = L⁻¹ * (a' : PairVal.MatR D) * L ∧ IsLoUni (a' : PairVal.MatR D) ∧
    ∃ b : PairVal.MatR D, IsUpUni b ∧ (a' : PairVal.MatR D) * ZhatOM Z * b = ZhatOM Z ∧
      ∀ p : PlF D, ∃ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
        Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧
        ∀ Z' : PairVal.MatR D, CntLocal.ZZP (M := M) δ u u' p (ZhatOM ((a' : PairVal.MatR D) * ZhatOM Z' * b)) =
          l * CntLocal.ZZP (M := M) δ u u' p Z' * ρ}

def CZ (Z L : PairVal.MatR D) : Subgroup (PairVal.GLR D) := Subgroup.closure (stZSet M δ u u' Z L)

def OrbStabE (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    PairVal.stabAut D u u' F0 what₂ γ F' L ≤ C (ZhatL (lf D F0) F') L ∧
      (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (C (ZhatL (lf D F0) F') L) =
        (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard ∧
      (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard ≠ 0

def ProdE (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    IdxRatio (PairVal.stabInt D u u' δ M w) (C (ZhatL (lf D F0) F') L) =
      ∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

theorem volIdxProd_of (hP : PrimeHyp D u (Tu D u')) (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D))
    (h1 : OrbStabE M δ u u' F0 what₂ C) (h2 : ProdE M δ u u' F0 what₂ C) : VolIdxProd M δ u u' F0 what₂ := by
  intro hA hT hR γ w F' L U hE hN
  have hH : HypE M δ u u' F0 what₂ γ w F' L U := ⟨hA, hT, hR, hP, hE, hN⟩
  obtain ⟨hle, hidx, hne⟩ := h1 γ w F' L U hH
  have hne' : (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (C (ZhatL (lf D F0) F') L) ≠ 0 := by
    rw [hidx]; exact hne
  have hco := Formalism.L2.SG.Pf.IndexCocycleOrbits.idxCocycle (PairVal.GLR D) (PairVal.stabInt D u u' δ M w)
    (PairVal.stabAut D u u' F0 what₂ γ F' L) (C (ZhatL (lf D F0) F') L) hle hne'
  have hv : PairVal.volIdx D u u' F0 what₂ δ M γ w F' L =
      IdxRatio (PairVal.stabInt D u u' δ M w) (PairVal.stabAut D u u' F0 what₂ γ F' L) := by rfl
  rw [hv, hco, hidx, h2 γ w F' L U hH]

end Formalism.L2.SG.Pf.ZsVolCut

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockEndMinorsOfCell
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGCut.PtPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frame_mem {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (hz : F.fl.z ∈ Λ) (hX : XLam Λ F = XS D F.fl) (b : Fin (D.R.rS + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_last]; exact hz
  | cast b =>
    rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_castSucc]
    have h : F.fl.e b ∈ XLam Λ F := by rw [hX]; exact Formalism.MainNotions.BridgeLemma₂.basis_vector_mem_span D F.fl b
    exact h.1

theorem zhatOM_isIntegral {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ) (i j : Fin (D.R.rS + 1)) :
    IsIntegral ℤ (ZhatOM (ZhatL F F') i j) := by
  obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hF i) (hF' j)
  have hZ : ZhatL F F' i j = (VS D).hT (frame F i) (frame F' j) := rfl
  have h1 : IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val)) := (isIntegral_one.neg).pow _
  show IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val) * ZhatL F F' i j)
  rw [hZ, ← hc]
  exact h1.mul (RingOfIntegers.isIntegral_coe c)


open Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms in
theorem blockEndMinors_of_cell {D : D7} (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hZ : ∀ i j, IsIntegral ℤ (Z i j)) (γ : Point D.host.E (D.R.rS + 1)) (hc : IsInCell Z γ) :
    BlockEndMinorsIntegral (toSig γ) := by
  obtain ⟨L, U, hL, hU, rfl⟩ := hc
  intro (a : Fin (toComp γ).length)
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_evaluation_fourth D.host.E (integralClosure ℤ D.host.E).toSubring (D.R.rS + 1)
    (toComp γ) (toT γ) (toT_ne γ) L U
    ⟨fun i => (hL i i).2 rfl, fun i j hij => (hL i j).1 hij⟩
    ⟨fun i => (hU i i).2 rfl, fun i j hij => (hU i j).1 hij⟩
    (by intro i j; rw [← ptMat_eq]; exact hZ i j)
  have := key.1 ((a : ℕ) + 1)
  show IsIntegral ℤ (IndexedMinorEntry (toComp γ).blocksFun (toT γ) a) ∧ IndexedMinorEntry (toComp γ).blocksFun (toT γ) a ≠ 0
  rw [E5minor_eq]
  exact this

theorem stepPoints_of_ctx
    (hOV : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, -, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := frame_mem _ hP.1.1 hP.2.2.2
  have hE := blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell
  rw [← hpt]
  exact hE

theorem stepPoints_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints :=
  stepPoints_of_ctx (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hOV D X Y u u')
    (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hAt D X Y u u')


end Formalism.L2.SG.NGCut.PtPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFwd
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : Formalism.BasicNotions.D7}

def OmCls {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  ∀ c : Fin (D.R.rS + 1) → D.host.E, (∀ a, (VS D).hT (F0.e a) (∑ b, c b • frame F'₂ b) = 0) →
    ∑ b, c b • (frame F' b - frame F'₂ b) ∈ Xsp (lf D F0)

variable (D)

def NMove : Prop :=
  ∀ {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS T'),
    ZhatL (lf D F0) F'₂ = ZhatL (lf D F0) F' → Gval (lf D F0) F' ≠ 0 → OmCls F0 F'₂ F' →
      ∃ n ∈ unipotentFrameFixers F0, Moves n F'₂ F'

end Defs

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def OmPart : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' → OmCls F0 F'₂ F'

def LocIn : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' → ∀ n ∈ unipotentFrameFixers F0, Moves n F'₂ F' →
        ∀ p, lattice₂ D Zd.M p (Formalism.HermitianLatticesTheory.gmap n.symm γ.lam) ∈
          locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p)

variable {u u' F0 what₂}

theorem fwdCut_image_gmap_symm (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (n : (VS D).V → (VS D).V) '' (Formalism.HermitianLatticesTheory.gmap n.symm Λ : Set (VS D).V) = (Λ : Set (VS D).V) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe, Set.mem_image, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨n.symm x, ⟨x, hx, rfl⟩, by simp⟩

theorem fwdCut_gval_congr {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (h : ZhatL F F₁ = ZhatL F F₂) : Gval F F₁ = Gval F F₂ := by
  simp only [Gval, Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl] at h ⊢
  rw [show Formalism.MainNotions.S.Zhat F.fl F₁.fl = Formalism.MainNotions.S.Zhat F.fl F₂.fl from h]

theorem fwdC_of (hrows : IsRowReps D F0 what₂) (h1 : NMove D) (h2 : OmPart Zd u u' F0 what₂)
    (h3 : LocIn Zd u u' F0 what₂) : FwdC Zd u u' F0 what₂ := by
  intro γ Z hC F'₂ φ φ' hS F' hP
  have hEZ := hP.1
  have hZ' : ZhatL (lf D F0) F' = Z := hEZ.2.2.2.2
  have hG : Gval (lf D F0) F' ≠ 0 := hEZ.1.2.2
  obtain ⟨n, hn, hm⟩ := h1 F0 F'₂ F' (hS.1.trans hZ'.symm) hG (h2 hrows γ Z hC F'₂ φ φ' hS F' hP)
  refine ⟨Formalism.HermitianLatticesTheory.gmap n.symm γ.lam, ⟨?_, h3 hrows γ Z hC F'₂ φ φ' hS F' hP n hn hm⟩, n, hn, hm,
    fwdCut_image_gmap_symm n γ.lam⟩
  have hlat : Submodule.IsFullLattice D.host.E γ.lam := (hrows.1 γ.lam γ.mem).1.1
  letI := Formalism.HermitianLatticesTheory.isomAct_lattice n.symm γ.lam hlat.toIsLattice
  refine ⟨?_⟩
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
  change Submodule.span D.host.E ((n.symm : (VS D).V →ₗ[D.host.E] (VS D).V) '' (γ.lam : Set _)) = ⊤
  rw [← Submodule.map_span, hlat.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 n.symm.surjective]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.NGCut
  Formalism.L2.SG.NGData

namespace Formalism.L2.SG.NGHTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nDelta {E : Type} [Field E] (r : ℕ) (γ : PN.Pts E r) : ℕ :=
  r * (r + 1) + ∑ a : Fin γ.1.length, endIdx γ a * (2 * r + 1 - endIdx γ a)

def HTPlace : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ {Cl' Nu : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl') (nml : TauC Y u u' → Nu)
        (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl' Nu), FamTie TS cls nml γ Fm →
        (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ≠ 0 ∧ ∀ a, endMin γ a ≠ 0) ∧ ∀ p : PlF D,
        ((Fm.FP p).PrimeTo → (Fm.FP p).Hp = 1) ∧
        (Fm.FP p).Hp =
          ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))) ^ ((2 * D.R.rS + 1 : ℝ) / 2) *
          ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p)) ^ (nDelta D.R.rS γ : ℝ) *
          ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)) ^ (-(1 / 2 : ℝ)) *
          ∏ a : Fin γ.1.length, (((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)))⁻¹

def HTDelta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

def HTTheta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

section Asm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem prod_inf_sq (x : E) : ∏ w : InfinitePlace E, w x ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyComplex.isComplex w).mult_eq_two]

theorem prod_inf (x : E) : ∏ w : InfinitePlace E, w x = Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← prod_inf_sq, Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun w _ => (w.1.nonneg x))]

theorem g_pow (g : ℝ) (hg : 0 < g) (f r : ℕ) :
    ((g ^ (2 * f))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) = (g ^ ((2 * r + 1) * f))⁻¹ := by
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast g (2 * f), ← Real.rpow_mul hg.le, ← Real.rpow_natCast g]
  congr 2
  push_cast
  ring

theorem inv_rpow_half (x : ℝ) (hx : 0 ≤ x) : (x⁻¹) ^ (-(1 / 2 : ℝ)) = Real.sqrt x := by
  rw [Real.inv_rpow hx, Real.rpow_neg hx, inv_inv, Real.sqrt_eq_rpow]

theorem hpt_eq [StarRing E] (r : ℕ) (γ : PN.Pts E r) (rd g : ℝ) (hg : 0 < g) (TT : ℕ) :
    HPt rd g TT γ =
      ((g ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) *
      ((rd ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ (nDelta r γ : ℝ) *
      (|((Algebra.norm ℚ (GPt TT γ) : ℚ) : ℝ)|⁻¹) ^ (-(1 / 2 : ℝ)) *
      ∏ a : Fin γ.1.length, (|((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹)⁻¹ := by
  set f := Fintype.card (InfinitePlace E) with hf
  rw [g_pow g hg f r, inv_rpow_half _ (abs_nonneg _), Real.rpow_natCast]
  simp only [inv_inv]
  unfold HPt NGPt NDPt
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf]
  have hD : ∀ a : Fin γ.1.length, ∏ w : InfinitePlace E,
      (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 =
      ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f * |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)| := by
    intro a
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf_sq]
  simp_rw [hD]
  rw [Finset.prod_mul_distrib]
  have hrd : ((rd ^ (2 * r * (r + 1)))⁻¹) ^ f *
      ∏ a : Fin γ.1.length, ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f =
      ((rd ^ (2 * f))⁻¹) ^ nDelta r γ := by
    simp only [← inv_pow, ← pow_mul, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
    congr 2
    unfold nDelta
    have e : ∀ i : Fin γ.1.length, 2 * (endIdx γ i * (2 * r + 1 - endIdx γ i)) * f =
        2 * f * (endIdx γ i * (2 * r + 1 - endIdx γ i)) := fun i => by ring
    simp only [e, ← Finset.mul_sum]
    ring
  rw [← hrd]
  ring

end Asm

section Main

open Formalism.MainNotions.S.LocNG

theorem hTie_of (hP : HTPlace) (hD : HTDelta) (hT : HTTheta) : Formalism.L2.SG.FamDefs.HTie := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a0, b0, hP2⟩ := hP Cg cb Cw cT CT C0
  refine ⟨a0, b0, ?_⟩
  intro C' Cl e1 e2 D large₂ X Y u u' hc Cl' Nu TS cls nml γ Fm hFT
  obtain ⟨⟨hG0, hD0⟩, hloc⟩ := hP2 C' Cl e1 e2 D large₂ X Y u u' hc TS cls nml γ Fm hFT
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, -, -, -, hgood, -⟩ := hFT
  have hOK : ∀ p, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hPF := (product_formula_e D.host.F D.host.E _ (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.s.atP).1 (zOf Y).M hOK
  obtain ⟨hAf, hAv⟩ := hT D (zOf Y)
  obtain ⟨hBf, hBv⟩ := hD D (zOf Y)
  obtain ⟨hCf, hCv⟩ := hPF _ hG0
  have hDf := fun a => hPF _ (hD0 a)
  classical
  set S : Finset (PlF D) := Fm.P ∪ hAf.toFinset ∪ hBf.toFinset ∪ hCf.toFinset ∪
    Finset.univ.biUnion (fun a => (hDf a).1.toFinset) with hS
  have hPS : Fm.P ⊆ S := fun p hp => by simp [hS, hp]
  have hsA : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p)))) ⊆ ↑S := fun p hp => by
    simp [hS, Set.Finite.mem_toFinset, hp]
  have hsB : (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsC : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsD : ∀ a, (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a))) ⊆ ↑S :=
    fun a p hp => by
      simp only [hS, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_union, Set.mem_iUnion,
        Set.Finite.coe_toFinset, Set.mem_univ, true_and]
      exact Or.inr ⟨a, trivial, hp⟩
  have hnn : ∀ p (x : (D.s.atP p).Ep), 0 ≤ ((zOf Y).M p).modK x := fun p x => ENNReal.toReal_nonneg

  have h1 : Fm.toL.Htot = ∏ p ∈ S, (Fm.FP p).Hp := by
    show ∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp = _
    rw [Finset.prod_coe_sort Fm.P (fun p => (Fm.FP p).Hp)]
    exact Finset.prod_subset hPS fun p _ hp => (hloc p).1 (hgood p hp)
  rw [h1, Finset.prod_congr rfl fun p _ => (hloc p).2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_comm (s := S) (t := Finset.univ),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))))
      (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)))
      (fun p _ => hnn p _)]
  simp_rw [Finset.prod_inv_distrib]
  rw [← finprod_eq_prod_of_mulSupport_subset _ hsA, ← finprod_eq_prod_of_mulSupport_subset _ hsB,
    ← finprod_eq_prod_of_mulSupport_subset _ hsC, hAv, hBv, hCv]
  have hDv : ∀ a, ∏ p ∈ S, ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)) =
      |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹ := fun a => by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (hsD a), (hDf a).2]
  simp_rw [hDv]
  have hg : (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    exact_mod_cast Nat.mul_pos h0 h1
  have hXg : (X.B.g : ℝ) = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by rw [X.g_eq]
  rw [hXg, ← Finset.prod_inv_distrib]
  exact hpt_eq D.R.rS γ D.host.rdE _ hg _

end Main

end Formalism.L2.SG.NGHTie
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupGlob
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def IntFr (U : PairVal.MatR D) : Prop :=
  ∀ c b : Fin (D.R.rS + 1), c < b → ∀ x ∈ FibQ.aaF D b, x * U c b ∈ FibQ.aaF D c

def TieG (U U' : PairVal.MatR D) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ c b : Fin (D.R.rS + 1),
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * (U c b - U' c b) = ((Lat.gS D : ℕ) : D.host.E) * o


variable (D) in
def GlobMove (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ Z₂ : PairVal.MatR D), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
    AtMat w Z₁ → AtMat w Z₂ → (∀ p, tupZ M δ u u' Z₁ p = tupZ M δ u u' Z₂ p) →
    ∃ U U' : PairVal.MatR D, IsUpUni U ∧ IsUpUni U' ∧ IntFr U ∧ IntFr U' ∧ TieG U U' ∧ Z₂ = U.conjTranspose * Z₁ * U'

end Formalism.L2.SG.Pf.TupGlob
end
end
