module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAd
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayer
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTriAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtInputOf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtInputOf
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameTypes
open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame
set_option maxHeartbeats 4000000 in
theorem mtInput_of_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (M' : MtFam D') (hM : HEq (mtL nt.L nt.M) M') :
    ∃ tup Q, MtInput D' M' tup Q := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have hm : mtL L M = M' := eq_of_heq hM
  subst hm
  exact ⟨tp.tup, C.Q, { mt with }⟩
variable {D : D7}
section Read
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}
end Read
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        ∃ (f : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV → ℂ) (J : Subgroup (Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV)) (χ : J →* ℂˣ)
          (ψ₀ : AddChar (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E)) ℂ)
          (ξ : (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E))ˣ →* ℂˣ),
          f ≠ 0 ∧ Formalism.L2.NG.IsPsi0 s' ψ₀ ∧ Formalism.L2.NG.LevelUni J χ s' (w.st Z).toD7.R.r ψ₀ ξ ∧
          (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
          (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, ReciprocityTheory.Aut.TrivOutside {s'.v} κ → ∀ y : GL (Fin (w.st Z).toD7.R.nV) (GlobalTheory.CenFrame.Os s'),
        GlobalTheory.CenFrame.IsCompOf s' κ y →
      ((∀ i j : Fin (w.st Z).toD7.R.nV, ((w.st Z).toD7.R.r ≤ i.val → j.val < (w.st Z).toD7.R.r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro ad i s k hs hnt s' φ b hPg _ hfr
  obtain ⟨tup, Q, hin⟩ := _root_.GlobalTheory.FrameTypes.mtInput_of_alt c.a.nt c.a.all.gal.mt c.a.mt_eq
  obtain ⟨plg, iso, h1, -⟩ := t.r.z.pins.keep.grp
  exact types_of (D := (w.st Z).toD7) ad hin t.r.z.pins.char.base.lev t.r.z.pins.char.base.grp.levels i _ k hs hnt s' φ b hPg
    ⟨(plg.symm ⟨s'.w, hPg⟩).1, (plg.symm ⟨s'.w, hPg⟩).2, by rw [← h1, plg.apply_symm_apply]⟩ hfr

end GlobalTheory.FrameTypes
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtInputOfStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_frame_split_nontrivial_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        ∃ (f : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV → ℂ) (J : Subgroup (Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV)) (χ : J →* ℂˣ)
          (ψ₀ : AddChar (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E)) ℂ)
          (ξ : (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E))ˣ →* ℂˣ),
          f ≠ 0 ∧ Formalism.L2.NG.IsPsi0 s' ψ₀ ∧ Formalism.L2.NG.LevelUni J χ s' (w.st Z).toD7.R.r ψ₀ ξ ∧
          (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
          (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, ReciprocityTheory.Aut.TrivOutside {s'.v} κ → ∀ y : GL (Fin (w.st Z).toD7.R.nV) (GlobalTheory.CenFrame.Os s'),
        GlobalTheory.CenFrame.IsCompOf s' κ y →
      ((∀ i j : Fin (w.st Z).toD7.R.nV, ((w.st Z).toD7.R.r ≤ i.val → j.val < (w.st Z).toD7.R.r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) := by
  first | exact @_root_.GlobalTheory.FrameTypes.main_alt_alt | exact _root_.GlobalTheory.FrameTypes.main_alt_alt | (intros; apply _root_.GlobalTheory.FrameTypes.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreBis
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreBis
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.ResThree
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ PP ∈ t.r.z.R.Pg, ∃ x : Formalism.L2.DIV.kP PP, x ≠ 0 ∧ x ≠ 1 := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro PP hPP
  obtain ⟨plg, iso, -, -, -, -⟩ := t.r.z.pins.keep.grp
  obtain ⟨h0, h1⟩ := two_ne_zero_one _ (GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients.three_le_g (w.st Z).toD7 (plg.symm ⟨PP, hPP⟩).1)
  have e := iso (plg.symm ⟨PP, hPP⟩)
  rw [Equiv.apply_symm_apply] at e
  exact ⟨e 2, fun h => h0 (e.injective (by rw [h, map_zero])),
    fun h => h1 (e.injective (by rw [h, map_one]))⟩
end GlobalTheory.ResThree
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreBisStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_ne_zero_ne_one_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ PP ∈ t.r.z.R.Pg, ∃ x : Formalism.L2.DIV.kP PP, x ≠ 0 ∧ x ≠ 1 := by
  first | exact @_root_.GlobalTheory.ResThree.main_alt_alt | exact _root_.GlobalTheory.ResThree.main_alt_alt | (intros; apply _root_.GlobalTheory.ResThree.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTriAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameBlockTriangular
theorem blockTri_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (w.st Z).toD7.R.r) := by
  intro hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.central_frame_split_nontrivial_at_alt hL) (_root_.GlobalTheory.T.exists_residue_ne_zero_ne_one_at_member hL)) ?_
  intro K B f T w Z Wt p0 t nch n c h ad i s k hs hN s' φ b hP hres hfr
  obtain ⟨F, J, χ, ψ₀, ξ, hF, hψ, hJ, hFJ, hS⟩ := h.1 ad i s k hs hN s' φ b hP hres hfr
  have hr : 2 ≤ (w.st Z).toD7.R.r := by
    have h1 := (w.st Z).toD7.R.two_le_m
    have h2 := (w.st Z).toD7.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact GlobalTheory.T.conjugate_blockUpper_of_eigenfunction_unipotentType (t := (w.st Z).toD7.R.t) rfl hr s' φ hres (h.2 _ hP) F hF J χ ψ₀ ξ hψ hJ hFJ b hS
end GlobalTheory.FrameBlockTriangular
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTriAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_frame_split_place_nontrivial_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (w.st Z).toD7.R.r) := by
  first | exact @_root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt | exact _root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt | (intros; apply _root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelFinEMemDivisorStandard
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameInt
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b :=
  fun hL => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ ad k s =>
    frame_of (D := (w.st Z).toD7) t.r.z.R.toLevCh t.r.z.pins.char.base.lev t.r.Y.hF k (ad.PV k) (ad.std k) s
end GlobalTheory.FrameInt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_finE_mem_divisor_standard_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b := by
  first | exact @_root_.GlobalTheory.FrameInt.main_alt_alt | exact _root_.GlobalTheory.FrameInt.main_alt_alt | (intros; apply _root_.GlobalTheory.FrameInt.main_alt_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMem
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.BlockLiftFrame
open ReciprocityTheory.Aut GlobalTheory.CenFrame
section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Local
end GlobalTheory.BlockLiftFrame
end
theorem GlobalTheory.BlockLiftFrame.atMem_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro s
  obtain ⟨plg, iso, h1, -, -, h4⟩ := t.r.z.pins.keep.grp
  exact GlobalTheory.BlockLiftFrame.exists_blockLift (w.st Z).toD7 (t.r.z.lev.is.Q_pl s) t.r.z.R.eG t.r.z.cG ⟨plg, iso, h1, h4⟩
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.g0_lift_unitary_central_frame_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  first | exact @_root_.GlobalTheory.BlockLiftFrame.atMem_alt | exact _root_.GlobalTheory.BlockLiftFrame.atMem_alt | (intros; apply _root_.GlobalTheory.BlockLiftFrame.atMem_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayer
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.CenLocAt
set_option maxHeartbeats 4000000 in
theorem frameAt_of_layer_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  intro hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.level_finE_mem_divisor_standard_alt hL) (_root_.GlobalTheory.T.central_frame_split_place_nontrivial_alt hL)) (_root_.GlobalTheory.T.g0_lift_unitary_central_frame_alt hL)) ?_
  intro K B f T w Z Wt p0 t nch n c h ad i s k hs
  obtain ⟨⟨hA, hB⟩, hC⟩ := h
  obtain ⟨L, hL1, hU, hLc⟩ := hC s
  obtain ⟨hSt, hFR⟩ := hA ad k s
  refine ⟨L, hL1, fun hN => ?_⟩
  refine GlobalTheory.T.exists_conj_parahoric_block_lift t.r.z.R t.r.z.cG k s (ad.PV k) L hU hSt (fun PP hPP => ?_) hLc
  obtain ⟨s', φ, b, hw, hres, hfr⟩ := hFR PP hPP
  exact ⟨s', φ, b, hw, hres, hfr, fun hP => hB ad i s k hs hN s' φ b (hw ▸ hP) hres hfr⟩
end GlobalTheory.CenLocAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayerStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  first | exact @_root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | exact _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | (intros; apply _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenRatAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenRatAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenRatAt
section Main
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}
end Main
theorem cenRat_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ hR _ => hR.elim fun r => cenRat_of t r
end GlobalTheory.CenRatAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenRatAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenRat_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  first | exact @_root_.GlobalTheory.CenRatAt.cenRat_at_alt | exact _root_.GlobalTheory.CenRatAt.cenRat_at_alt | (intros; apply _root_.GlobalTheory.CenRatAt.cenRat_at_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActReadAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActReadAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenLocAt
section Gen
open _root_.Formalism.L2.DIV _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
end Gen
theorem actRead_at_mem_of_recT : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ =>
    actRead_of t.r.Y t.r.z.pins.char.base.models t.r.z.pins.char.base.grp.red_L t.r.intersectionNumber_baseChange.ok
end GlobalTheory.CenLocAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActReadAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actRead_at_member_of_recT : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y := by
  first | exact @_root_.GlobalTheory.CenLocAt.actRead_at_mem_of_recT | exact _root_.GlobalTheory.CenLocAt.actRead_at_mem_of_recT | (intros; apply _root_.GlobalTheory.CenLocAt.actRead_at_mem_of_recT <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAd
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenLocAt
theorem exists_ad_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ c => Nonempty (MtAd t.r.Y c.a.all.gal.mt) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE _ _ => hE.elim fun e => ⟨_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.ad e⟩
set_option maxHeartbeats 2000000 in
theorem cenLoc_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenRat_at_members hL) (_root_.GlobalTheory.T.actRead_at_member_of_recT hL)) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members hL) (_root_.GlobalTheory.CenLocAt.exists_ad_alt hL)))
    fun _ _ _ _ _ _ _ _ t _ _ _ h => h.2.2.elim fun ad => cenLoc_of t.r.Y t.r.z.cG _ ad h.1.1 h.1.2 (h.2.1 ad)
end GlobalTheory.CenLocAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAdStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenLoc_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := by
  first | exact @_root_.GlobalTheory.CenLocAt.cenLoc_at_member | exact _root_.GlobalTheory.CenLocAt.cenLoc_at_member | (intros; apply _root_.GlobalTheory.CenLocAt.cenLoc_at_member <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenIntAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenIntAt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenIntAtLoc
open _root_.Formalism.L2.DIV
end GlobalTheory.CenIntAtLoc
namespace GlobalTheory.CenIntAtLoc
theorem cenInt_at_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.CenInt (w.D Z) := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ w Z _ _ t _ _ _ _ _ hR _ => ?_
  obtain ⟨r⟩ := hR
  refine cenInt_of_allT r.all (InfinitePlace.mk (w.st Z).B.embLL) (GlobalTheory.Mem.R3.OkVals.isConjAt_embLL _) (fun k τ => ?_) (fun k τ => ?_)
  · exact (Formalism.L2.Col.mtK_rat _ _ _ τ.1 t.hX ((k : ℕ) + 1)).posH _ _
  · exact Formalism.L2.Col.unipotentActionClassSum_good _ _ _ τ.1 t.hX ((k : ℕ) + 1) _
end GlobalTheory.CenIntAtLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenIntAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenInt_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.CenInt (w.D Z) := by
  first | exact @_root_.GlobalTheory.CenIntAtLoc.cenInt_at_alt | exact _root_.GlobalTheory.CenIntAtLoc.cenInt_at_alt | (intros; apply _root_.GlobalTheory.CenIntAtLoc.cenInt_at_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenAtLoc
theorem zlStable_at_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.ZLStable (w.D Z) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR _ => hR.elim fun r => zlStable_of_allT r.all
theorem cen_loc_zl_stable_cen_int : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => CenLoc (w.D Z) c.a.all.gal.mt ∧ GlobalTheory.PendOf.ZLStable (w.D Z) ∧ GlobalTheory.PendOf.CenInt (w.D Z) := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenLoc_at_members hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.CenAtLoc.zlStable_at_alt hL) (_root_.GlobalTheory.T.cenInt_at_members hL))
end GlobalTheory.CenAtLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => CenLoc (w.D Z) c.a.all.gal.mt ∧ GlobalTheory.PendOf.ZLStable (w.D Z) ∧ GlobalTheory.PendOf.CenInt (w.D Z) := by
  first | exact @_root_.GlobalTheory.CenAtLoc.cen_loc_zl_stable_cen_int | exact _root_.GlobalTheory.CenAtLoc.cen_loc_zl_stable_cen_int | (intros; apply _root_.GlobalTheory.CenAtLoc.cen_loc_zl_stable_cen_int <;> assumption)
end
end
