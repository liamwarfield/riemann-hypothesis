module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RMeasP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopVol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem root_fst_lt (w : Point D.host.E (D.R.rS + 1)) (q : GlobalTheory.LoopV.roots (ptMat w)) : q.1.1.1 < D.R.rS := by
  have hq := q.2
  simp only [GlobalTheory.LoopV.roots, Finset.mem_filter] at hq
  have h := hq.2.1
  have h2 := q.1.2.2
  rw [Fin.lt_def] at h
  omega

def ratCoord (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s y : X.B.I.Ginf) : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ :=
  fun τ q => Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε (X.pl.symm τ))
    (Formalism.L2.SG.HidaSetting.rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
    (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ)) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) q.1.2)

theorem ratCoord_cont (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s : X.B.I.Ginf) : Continuous (ratCoord X u' w γ s) := by
  unfold ratCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun τ => continuous_pi fun q => ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply _).comp
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)))

end GlobalTheory.LoopVol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRows
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRows
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.NGClass

theorem vec_eq_zero_of_oo {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word} (t : TauC Y u u')
    (h : OOt t = 0) : (Y.tO u u').vec t = 0 := by
  show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold vec ampN
  rw [h]
  simp
  rfl

theorem ngClass_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ (∀ t ∈ (Y.tO u u').ngSet, ∀ t' ∈ (Y.tO u u').ngSet, clsOf Y u u' t = clsOf Y u u' t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') ∧ ∀ t : TauC Y u u', (Y.tO u u').vec t ≠ 0 → t.relevant := by
  intro D X Y u u' hT
  refine ⟨fun t ht => ?_, fun t ht t' ht' heq => ?_, fun t hv => ?_⟩
  · intro h0
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos h0]
  · obtain ⟨hR, -, -⟩ := Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds D X Y u u' hT
    have hm : t' ∈ clsOf Y u u' t' := ⟨ht', rfl, hR t' ht'⟩
    rw [← heq] at hm
    exact hm.2.1.symm
  · by_contra hr
    exact hv (vec_eq_zero_of_oo Y t
      (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
        Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
        Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
        Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr))

end GlobalTheory.NGClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRowsStatement
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGeneric_family_classes_determine_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ (∀ t ∈ (Y.tO u u').ngSet, ∀ t' ∈ (Y.tO u u').ngSet, clsOf Y u u' t = clsOf Y u u' t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') ∧ ∀ t : TauC Y u u', (Y.tO u u').vec t ≠ 0 → t.relevant := by
  first | exact @GlobalTheory.NGClass.ngClass_rows | exact GlobalTheory.NGClass.ngClass_rows | (intros; apply GlobalTheory.NGClass.ngClass_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinXOfDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalHHX
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsFiniteDim

theorem finiteDimensional_HHX : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FiniteDimensional ℂ (HHX X) := by
  intro hHC D X h
  exact hHC X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re X.B.e_adm.1
    X.B.e_adm.2.2.2.2.1 X.B.Re_spec
    X.B.H X.B.σ (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.w
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec

end GlobalTheory.RowsFiniteDim
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory.FinitenessBundle

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_Gflag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} (n m : ℕ)
    (F : FlagG S r (n : E)) (F' : FlagG S r (m : E)) : star (Gflag F F') = Gflag F F' := by
  simp only [Gflag, star_sub, star_mul', star_star, star_natCast]
  ring

theorem finX_of_decay : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X),
    Formalism.L2.SG.WuDecay.WuDecay X → Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FinX Y := by
  intro hR D X Y hW hI
  refine Formalism.L2.SG.Pf.finX_of_neat Y (fun u => Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) (fun u => ?_)
    (GlobalTheory.RowsFiniteDim.finiteDimensional_HHX hR D X hI) (fun u u' t => Formalism.L2.SG.Pf.FinXP.fibFin_holds D X Y u u' t)
    (fun u u' s₁ s₂ s₁' s₂' => Formalism.L2.SG.Pf.FinXP.pairIndep_of Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds D X Y u u' s₁ s₂ s₁' s₂')
    (fun u u' t => ?_) Formalism.L2.SG.Closed.VolPosC_holds
  · have hL : X.LevelSubgroupNormalized := Formalism.L2.SG.Closed.level_subgroup_properties X
    exact Formalism.L2.SG.Closed.InHHC_holds D X Y u hI (Formalism.L2.SG.Closed.FoldOKC_holds Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds D X Y u hL hW)
  · rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    exact star_Gflag _ _ _ _

end GlobalTheory.FinitenessBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermLatticeBaseFramesOfBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermLatticeBaseFramesOfBasePoint
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem tg_of_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  intro D X Y u u' F F' w hZ hG t hpt
  have hcF : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), 1, ?_, ?_, by rw [hZ]; simp⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne, fun h => h ▸ Matrix.one_apply_eq i⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq i⟩
  have hGw := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq F F' w hcF
  have hw : Formalism.L2.SG.PairVal.ptOf t.toTerm = w := Formalism.L2.SG.NGCut.NormalVectorPairings.toPts_inj _ _ hpt
  have hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
    by_contra h
    apply hG
    rw [← hGw, ← hpt]
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dite_eq_right h]
    exact Formalism.L2.SG.NGCut.NormalVectorPairings.GPt_junk D u u'
  obtain ⟨F'', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hex
  rw [hw] at hcell
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨F'', hP⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ := hmk
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ _ _).1 hmk'
  have hcell' : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w := ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).2.1 _ _ hrel w).1 hcell
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h0
    apply hG
    rw [← hGw]
    exact (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') _ _ w hcell').trans h0
  obtain ⟨-, γ, hγ, ⟨A, hA, hc⟩, ⟨B, hB, hd⟩⟩ := GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D (X.Fu u)) F t.frame F' w
    (Formalism.L2.SG.Corank.tu_ne_zero u) (Formalism.L2.SG.Corank.tu_ne_zero u') hGt hcell' hZ
  exact ⟨Formalism.HermitianLatticesTheory.gmap γ t.lam, γ, ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F.fl hA hc a⟩,
    ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F'.fl hB hd a⟩, rfl⟩

end GlobalTheory.Unfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermLatticeBaseFramesOfBasePointStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_termLattice_baseFrames_of_basePoint : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  first | exact @GlobalTheory.Unfold.tg_of_base_point | exact GlobalTheory.Unfold.tg_of_base_point | (intros; apply GlobalTheory.Unfold.tg_of_base_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddIsotropicSpanMemLocallyStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddIsotropicSpanMemLocallyStandardLattice
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.IsotropicLift

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def kerR (H : HermSp M V) (w : V) : Submodule E V where
  carrier := {v | H.h v w = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_add_left, ha, hb, add_zero]
  zero_mem' := H.h_zero_left w
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_smul_left, hv, mul_zero]

theorem h_swap_zero (H : HermSp M V) {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h]; simp

theorem X_le_perp (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  intro x hx
  have hk : H.X Fr.f ≤ kerR H (Fr.f b.castSucc) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Fr.h_iso a.castSucc b.castSucc (Or.inl (Fin.castSucc_ne_last a))
  exact h_swap_zero H (hk hx)

theorem sub_mem_X_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    {v : V} (hv : v ∈ H.perp (H.X Fr.f)) : n v - v ∈ H.X Fr.f := by
  have hXP := X_le_perp H Fr
  suffices key : ∀ g ∈ Fr.N, ∀ v ∈ H.perp (H.X Fr.f), g v - v ∈ H.X Fr.f ∧ g.symm v - v ∈ H.X Fr.f from
    (key n hn v hv).1
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hu, -, hperp⟩ := hg
    intro v hv
    refine ⟨hperp v hv, ?_⟩
    have hw : g.symm v ∈ H.perp (H.X Fr.f) := by
      intro x hx
      have hgx : g x ∈ H.X Fr.f := by
        have := hperp x (hXP hx)
        have e : g x = (g x - x) + x := by abel
        rw [e]; exact Submodule.add_mem _ this hx
      rw [← hu (g.symm v) x, LinearEquiv.apply_symm_apply]
      exact hv _ hgx
    have h1 := hperp _ hw
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : g.symm v - v = -(v - g.symm v) := by abel
    rw [e]; exact Submodule.neg_mem _ h1
  | one =>
    intro v _
    exact ⟨by simp, by show v - v ∈ _; simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    intro v hv
    have hm : ∀ x, (g₁ * g₂) x = g₁ (g₂ x) := fun _ => rfl
    have hms : ∀ x, (g₁ * g₂).symm x = g₂.symm (g₁.symm x) := fun _ => rfl
    obtain ⟨a2, b2⟩ := ih₂ v hv
    obtain ⟨a1, b1⟩ := ih₁ v hv
    have hv2 : g₂ v ∈ H.perp (H.X Fr.f) := by
      have e : g₂ v = (g₂ v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP a2) hv
    have hv1 : g₁.symm v ∈ H.perp (H.X Fr.f) := by
      have e : g₁.symm v = (g₁.symm v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP b1) hv
    refine ⟨?_, ?_⟩
    · rw [hm]
      have e : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₁ _ hv2).1 a2
    · rw [hms]
      have e : g₂.symm (g₁.symm v) - v = (g₂.symm (g₁.symm v) - g₁.symm v) + (g₁.symm v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₂ _ hv1).2 b1
  | inv g _ ih =>
    intro v hv
    exact ⟨(ih v hv).2, (ih v hv).1⟩

theorem z_mem_LamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)}
    (hL : Fr.IsInner L) : Fr.z ∈ Fr.LamStd L := by
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  have hs : ∀ a, H.h Fr.z (Fr.es a) = 0 := fun a => h_swap_zero H (Fr.h_sz a)
  have he : ∀ a, H.h Fr.z (Fr.e a) = 0 := fun a =>
    Fr.h_iso (Fin.last r) a.castSucc (Or.inr (Fin.castSucc_ne_last a))
  refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, xz, ?_, hxzL⟩
  · rw [hs a]; exact zero_mem _
  · rw [he a]; exact zero_mem _
  · rw [hxz]
    simp [FrameD.prF, hs, he]

end Gen

variable {D : D7}

theorem exists_add_mem : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D)
    (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS),
    (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D,
    Submodule.IsLattice D.host.E Λ →
    (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) →
    ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  intro D T G Z A hA Λ hΛ hloc
  obtain ⟨π, hπX, hπmem⟩ : ∃ π : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ G.fl.X, π x = x) ∧ ∀ x, π x ∈ G.fl.X := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective G.fl.X.subtype (Submodule.ker_subtype _)
    refine ⟨G.fl.X.subtype ∘ₗ g, fun x hx => ?_, fun x => (g x).2⟩
    have := congrArg (fun f => ((f ⟨x, hx⟩ : G.fl.X) : (VS D).V)) hg
    exact this
  obtain ⟨Λ₁, hΛ₁⟩ : ∃ N : LV D, N = Λ ⊔ Submodule.span (𝓞 D.host.E) {G.fl.z} := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ N : LV D, N = Λ ⊔ Λ₁.map (π.restrictScalars (𝓞 D.host.E)) := ⟨_, rfl⟩
  have hfg : Λ₂.FG := by
    rw [hΛ₂, hΛ₁]; exact hΛ.fg.sup ((hΛ.fg.sup (Submodule.fg_span_singleton _)).map _)
  have hz : G.fl.z ∈ Λ₂ := by
    refine GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z hfg fun p => ?_
    obtain ⟨n, hn, L, hL, hlat⟩ := hloc p
    have hzp : (A p).z = baseChange₂ D p G.fl.z := by
      show (A p).f (Fin.last _) = _
      rw [hA p]
      simp [frFac, frame, FlagG.fvec]
    have hperp : (A p).z ∈ (locH Z p).perp ((locH Z p).X (A p).f) := by
      obtain ⟨-, -, xz, hxz, -, -⟩ := hL
      rw [← hxz]; exact xz.2
    have hnz : n (A p).z ∈ lattice₂ D Z.M p Λ := by
      rw [hlat]
      exact Submodule.mem_map_of_mem (z_mem_LamStd _ (A p) hL)
    have hxX := sub_mem_X_of_mem_N _ (A p) hn hperp
    have hfix : (locH Z p).X (A p).f ≤ LinearMap.eqLocus (GlobalTheory.LocExt.locEnd p π) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show (GlobalTheory.LocExt.locEnd p π) ((A p).f a.castSucc) = (A p).f a.castSucc
      rw [hA p]
      rw [map_smul, GlobalTheory.LocExt.locEnd_bcP, GlobalTheory.LocExt.frame_castSucc,
        hπX _ (Submodule.subset_span ⟨a, rfl⟩)]
      show _ = frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)
      rw [GlobalTheory.LocExt.frame_castSucc]
    have hx1 : n (A p).z - (A p).z ∈ lattice₂ D Z.M p Λ₁ := by
      rw [hΛ₁]
      refine Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz) ?_
      rw [hzp]
      exact Submodule.subset_span ⟨G.fl.z, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), rfl⟩
    have hx2 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) ∈ lattice₂ D Z.M p (Λ₁.map (π.restrictScalars (𝓞 D.host.E))) := by
      rw [GlobalTheory.FrameProj.localLattice_map Z p π (GlobalTheory.LocExt.locEnd p π) (fun x => (GlobalTheory.LocExt.locEnd_bcP p π x).symm) Λ₁]
      exact Submodule.mem_map_of_mem hx1
    have hx3 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) = n (A p).z - (A p).z := hfix hxX
    rw [hx3] at hx2
    have e : baseChange₂ D p G.fl.z = n (A p).z - (n (A p).z - (A p).z) := by rw [hzp]; abel
    rw [e, hΛ₂]
    exact Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz)
      (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hx2)
  rw [hΛ₂] at hz
  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.1 hz
  obtain ⟨w, -, rfl⟩ := hy
  refine ⟨-(π w), Submodule.neg_mem _ (hπmem w), ?_⟩
  have e : G.fl.z + -(π w) = l := by
    rw [← hly]; simp
  rw [e]; exact hl

end GlobalTheory.IsotropicLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddIsotropicSpanMemLocallyStandardLatticeStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_add_isotropicSpan_mem_locallyStandardLattice : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  first | exact @GlobalTheory.IsotropicLift.exists_add_mem | exact GlobalTheory.IsotropicLift.exists_add_mem | (intros; apply GlobalTheory.IsotropicLift.exists_add_mem <;> assumption)
end
end
