module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetZhatSwapUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRat

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SendsB
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BetaI

def SendsB (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (m : (VS D).V) : Prop :=
  ∀ (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
    ψ ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) = (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩

end BetaI

variable (u u' F0 what₂)

def PinOm : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ p : PlF D, BetaI.SendsB Zd p γ F'₂ (φ' p) β₀ (Gom (frame (lf D F0)) (frame (repF γ)))

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartialIsometryExtension
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def PartialIsometryExtension : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (w : (VS D).V), w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus) →
        BetaI.SendsB Zd p γ F'₂ (φ' p) β₀ w

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsotropicSpanOrthogonalAnisotropicVector
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem hsw' (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem fvec_cs {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (i : Fin D.R.rS) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

theorem fvec_last {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : F.fvec (Fin.last D.R.rS) = F.z := by
  simp [FlagG.fvec]

theorem hff {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [fvec_last, F.z_norm, if_pos ⟨rfl, rfl⟩]
    | cast j =>
      rw [fvec_last, fvec_cs, if_neg (fun h => Fin.castSucc_ne_last j h.2), hsw', F.z_orth, star_zero]
  | cast i =>
    rw [if_neg (fun h => Fin.castSucc_ne_last i h.1)]
    induction b using Fin.lastCases with
    | last => rw [fvec_cs, fvec_last, F.z_orth]
    | cast j => rw [fvec_cs, fvec_cs, F.e_iso]

theorem iso_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x y : (VS D).V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    (VS D).hT x y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, F.e_iso]

theorem isotropicSpan_orthogonal_anisotropicVector {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT x F.z = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, F.z_orth]

theorem z_orth_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT F.z x = 0 := by
  rw [hsw', isotropicSpan_orthogonal_anisotropicVector F hx, star_zero]

theorem Xplus_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    F.Xplus = Submodule.span D.host.E (Set.range F.fvec) := by
  apply le_antisymm
  · apply sup_le
    · rw [FlagG.X, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.castSucc, fvec_cs F i⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨Fin.last _, fvec_last F⟩
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    induction a using Fin.lastCases with
    | last => rw [fvec_last]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    | cast i => rw [fvec_cs]; exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalOrthogonalHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameMemUUE
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameActMemXplus
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_mem_Xplus {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (b : Fin (D.R.rS + 1)) :
    frameAct (frame G) ξ b ∈ G.fl.Xplus := by
  rw [SpanOmPf.Xplus_eq]
  show ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • frame G a ∈ _
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem form_zero (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) {v : (VS D).V}
    (hv : v ∈ F0.Xplus ⊔ (repF γ).fl.Xplus) (c : (D.s.atP p).Ep) :
    LocFacts₂ Zd.M p (baseChange₂ D p w) (c • baseChange₂ D p v) = 0 := by
  rw [LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, map_zero,
    mul_zero]

theorem baseChange_mem_W0 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) :
    baseChange₂ D p w ∈ (locH Zd p).W0 (tLoc Zd p γ).f (tLoc Zd p γ).f' := by
  show ∀ x ∈ (locH Zd p).Xp (tLoc Zd p γ).f ⊔ (locH Zd p).Xp (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p w) x = 0
  intro x hx
  rw [h_eq]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  rw [LocFacts.localForm_add_right]
  have hA : LocFacts₂ Zd.M p (baseChange₂ D p w) a = 0 := by
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf]
      refine form_zero Zd p γ hw (Submodule.mem_sup_left ?_) _
      rw [SpanOmPf.Xplus_eq]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  clear ha
  have hB : LocFacts₂ Zd.M p (baseChange₂ D p w) b = 0 := by
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf']
      exact form_zero Zd p γ hw (Submodule.mem_sup_right (frameAct_mem_Xplus _ _ i)) _
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  rw [hA, hB, add_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem localSign_sq (p : PlF D) (a : Fin (D.R.rS + 1)) : TermLoc.sgnP D p a * TermLoc.sgnP D p a = 1 := by
  unfold TermLoc.sgnP
  split
  · rename_i sg _
    rw [← map_mul, Prod.mk_mul_mk, Formalism.L2.SG.Pf.FibD.neg_one_pow_sq, one_mul]
    exact map_one sg.e.symm
  · exact one_mul 1

theorem hu_all (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) :=
  IsUnit.mul ⟨Units.mkOfMulEqOne _ _ (localSign_sq p a), rfl⟩
    (Formalism.L2.SG.Pf.StabShape.frFac_unit Zd.δ Zd.M (Zd.agree p) a)

theorem frame_mem_UUE {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (G : LFlag (D.sp.Y 0) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    frame G b ∈ UUE Λ F (liftF G) := by
  induction b using Fin.lastCases with
  | last =>
    rw [frame_lastG]
    apply Submodule.subset_span
    show G.fl.z ∈ (UU Λ F (liftF G) : Set (VS D).V)
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  | cast i =>
    rw [frame_csG]
    haveI := hΛ
    obtain ⟨s, hs, hsv⟩ := Formalism.L2.SG.Pf.exists_smul_mem Λ (G.fl.e i)
    have hX : s • G.fl.e i ∈ UU Λ F (liftF G) := by
      refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hsv, ?_⟩)
      show s • G.fl.e i ∈ (Xsp (liftF G) : Set (VS D).V)
      exact Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨i, rfl⟩)
    have hs' : ((s : D.host.E)) ≠ 0 := by exact_mod_cast hs
    have e : G.fl.e i = ((s : D.host.E))⁻¹ • (s • G.fl.e i) := by
      rw [← algebraMap_smul (R := 𝓞 D.host.E) D.host.E s (G.fl.e i), smul_smul]
      show G.fl.e i = (((s : D.host.E))⁻¹ * algebraMap (𝓞 D.host.E) D.host.E s) • G.fl.e i
      rw [show algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) from rfl, inv_mul_cancel₀ hs', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}


set_option maxHeartbeats 1000000 in
theorem localOrthogonal_holds : PartialIsometryExtension Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ₀ hfr hW0 hOm p w hw hm hm₂
  have hStar := hB.2.2.1
  have hT2 := hStar.2.1 p
  have hId := hT2.2.2.2.1

  have hwW := OrthogonalLocalComplement.baseChange_mem_W0 Zd p γ hw
  obtain ⟨w₂, hw₂, hs1, hs2⟩ := hId.2.2.1 (baseChange₂ D p w) hwW

  have hzrep : (repF γ).zt = (repF γ).fl.z := hB.2.2.2.2.2.2.1.1.2
  have hwHp : w ∈ Hp γ.lam (lf D F0) (repF γ) := by
    have hle := BwdBetaS.UUE_le_span γ.lam (lf D F0) (repF γ) rfl hzrep
    have hspan : Submodule.span D.host.E (Set.range (Sum.elim (lf D F0).fl.fvec (repF γ).fl.fvec)) =
        F0.Xplus ⊔ (repF γ).fl.Xplus := by
      rw [Set.Sum.elim_range, Submodule.span_union, SpanOmPf.Xplus_eq, SpanOmPf.Xplus_eq]
    rw [hspan] at hle
    show w ∈ orth (VS D) (UUE γ.lam (lf D F0) (repF γ))
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hw ⊢
    exact fun x hx => hw x (hle hx)
  obtain ⟨w₂g, hw₂g, hd1, hd2⟩ := hW0 w hwHp

  have hu := OrthogonalLocalComplement.hu_all Zd p
  have hwperp : baseChange₂ D p w ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) :=
    baseChange_mem_perp_sup Zd p γ ((PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw x
        (Submodule.mem_sup_left (le_sup_left (a := F0.X) (b := Submodule.span D.host.E {F0.z}) hx)))
  have hw₂perp : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp _ hw₂
  have hdiff1 : baseChange₂ D p w - w₂ ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have h := hs1 ⟨baseChange₂ D p w, hwperp⟩ ⟨w₂, hw₂perp⟩ rfl rfl
    have h1 : (φ p) ((locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p w, hwperp⟩) =
        (locH Zd p).mkW (tLoc Zd p γ).f ⟨w₂, hw₂perp⟩ := by
      have := h
      simp only [one_smul] at this
      exact this
    have e' : ∀ x, (φ p) x = x := fun x => by rw [hStar.2.2 p]; rfl
    exact LsDatumA.sub_mem_X_of_mkW_eq _ ((e' _).symm.trans h1)
  have hdiff2 : baseChange₂ D p w - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    rw [← map_sub]
    exact bcP_X Zd p γ hu hd1
  have hdX : w₂ - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := Submodule.sub_mem _ hdiff2 hdiff1
    rwa [sub_sub_sub_cancel_left] at this
  have hd0 : ∀ a, (locH Zd p).h (w₂ - baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
    intro a
    have h1 : (locH Zd p).h w₂ (locF' Zd p F'₂ a) = 0 :=
      hw₂ _ (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (locH Zd p).h (baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
      rw [h_eq, locF'_eq, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
        (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw₂g _ (OrthogonalLocalComplement.frame_mem_UUE hB.2.2.2.1.1 (lf D F0) F'₂ a),
        map_zero, mul_zero]
    rw [OmL.h_sub_left, h1, h2, sub_zero]
  have hgen := (hB.2.2.2.1.2 p).1
  have hdet : IsUnit ((locH Zd p).Zhat (locF' Zd p F'₂) (tLoc Zd p γ).f).det := by
    have h := hgen.1.2.2.2.1
    rw [OmL.dl_last] at h
    rw [LsDatumA.Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
    exact h.map _
  have hd : w₂ - baseChange₂ D p w₂g = 0 :=
    OmL.uniq_loc (locH Zd p) (locF' Zd p F'₂) (tLoc Zd p γ).f hdet
      (le_trans (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩)) le_rfl hdX) hd0
  have hw₂eq : w₂ = baseChange₂ D p w₂g := sub_eq_zero.1 hd

  have hw₂perp' : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp' _ hw₂
  have h := hs2 ⟨baseChange₂ D p w, hm⟩ ⟨w₂, hw₂perp'⟩ rfl rfl
  have h' : (φ' p) ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p w, hm⟩) =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨w₂, hw₂perp'⟩ := by
    have := h
    simp only [one_smul] at this
    exact this
  rw [h']
  apply Submodule.Quotient.eq _ |>.2
  show w₂ - baseChange₂ D p (β₀ w) ∈ (locH Zd p).X (locF' Zd p F'₂)
  rw [hw₂eq, ← map_sub, show w₂g - β₀ w = -(β₀ w - w₂g) by abel, map_neg]
  exact Submodule.neg_mem _ (bcP_X' Zd p F'₂ hd2)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanOmHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OmegaHermitianZ
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')

theorem GZ_eq : GZ F.fvec F'.fvec = Zhat F F' := by
  ext a b; rfl

theorem GDl_eq (l : ℕ) : GDl F.fvec F'.fvec l = Dl F F' l := by
  unfold GDl Dl leadMinorE
  rw [GZ_eq]

theorem om_X' {y : (VS D).V} (hy : y ∈ F'.X) : (VS D).hT (Gom F.fvec F'.fvec) y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, ← fvec_cs F' i, om_pair, if_neg (Fin.castSucc_ne_last i), smul_zero]

theorem omega_hermitian_z : (VS D).hT (Gom F.fvec F'.fvec) F'.z = GDl F.fvec F'.fvec (D.R.rS + 1) := by
  rw [← fvec_last F', om_pair, if_pos rfl]

theorem f_om (a : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) =
      if a = Fin.last D.R.rS then star ((GZ F.fvec F'.fvec).adjugate (Fin.last _) (Fin.last _)) * -T else 0 := by
  unfold Gom
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul, hff]
  rw [Finset.sum_eq_single (Fin.last D.R.rS)]
  · by_cases ha : a = Fin.last D.R.rS
    · rw [if_pos ⟨ha, rfl⟩, if_pos ha]
    · rw [if_neg (fun h => ha h.1), if_neg ha, mul_zero]
  · intro b _ hb
    rw [if_neg (fun h => hb h.2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_om : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
    -T * (GDl F.fvec F'.fvec D.R.rS * star (GDl F.fvec F'.fvec D.R.rS)) := by
  have e : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
      ∑ a, (GZ F.fvec F'.fvec).adjugate (Fin.last _) a * (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) := by
    conv_lhs => arg 1; unfold Gom
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [e, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [f_om, if_pos rfl, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r']
    ring
  · intro b _ hb
    rw [f_om, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_uniq (hdet : GDl F.fvec F'.fvec (D.R.rS + 1) ≠ 0) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range F.fvec)) (hxX : ∀ y ∈ F'.X, (VS D).hT y x = 0) :
    ∃ c : D.host.E, x = c • Gom F.fvec F'.fvec := by
  set c : D.host.E := star ((VS D).hT x F'.z / GDl F.fvec F'.fvec (D.R.rS + 1)) with hc
  refine ⟨c, sub_eq_zero.1 (eq_zero_of_orth_of_det_ne_zero F.fvec F'.fvec hdet
    (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (Gom_mem _ _))) fun b => ?_)⟩
  rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, om_pair]
  induction b using Fin.lastCases with
  | last =>
    rw [if_pos rfl, fvec_last, hc, star_star, div_mul_cancel₀ _ hdet, sub_self]
  | cast i =>
    rw [if_neg (Fin.castSucc_ne_last i), mul_zero, sub_zero, fvec_cs, hsw',
      hxX _ (Submodule.subset_span ⟨i, rfl⟩), star_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open SpanOmPf in
theorem spanOm_holds (D : Formalism.BasicNotions.D7) : SpanOm D := by
  intro T T' F F' hdet hG m hm
  set ω := Gom F.fvec F'.fvec with hω
  set Dd := GDl F.fvec F'.fvec (D.R.rS + 1) with hDd
  set Dr := GDl F.fvec F'.fvec D.R.rS with hDr
  have hD : Dd ≠ 0 := by rw [hDd, GDl_top', SpanOmPf.GZ_eq]; exact hdet
  have hG' : Dd * star Dd - T * T' * (Dr * star Dr) ≠ 0 := by
    rw [hDd, hDr, SpanOmPf.GDl_eq, SpanOmPf.GDl_eq]; exact hG
  set W0 := orth (VS D) (F.Xplus ⊔ F'.Xplus) with hW0
  set U := F'.X ⊔ W0 ⊔ Submodule.span D.host.E {F'.z, ω} with hU
  have key : ∀ u ∈ orth (VS D) U, u ∈ F'.X := by
    intro u hu
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hu
    have h1 : ∀ y ∈ F'.X, (VS D).hT y u = 0 := fun y hy =>
      hu y (Submodule.mem_sup_left (Submodule.mem_sup_left hy))
    have h2 : ∀ w ∈ W0, (VS D).hT w u = 0 := fun w hw =>
      hu w (Submodule.mem_sup_left (Submodule.mem_sup_right hw))
    have h3 : (VS D).hT F'.z u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _)))
    have h4 : (VS D).hT ω u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
    have hP : u ∈ F.Xplus ⊔ F'.Xplus :=
      BwdNA.mem_of_orth_orth (VS D) _ (fun w hw => by rw [SpanOmPf.hsw', h2 w hw, star_zero])
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hP
    obtain ⟨y', hy', s, hs, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hs
    have hxX : ∀ y0 ∈ F'.X, (VS D).hT y0 x = 0 := by
      intro y0 hy0
      have := h1 y0 hy0
      rw [map_add (f := _), map_add (f := _), SpanOmPf.iso_X F' hy0 hy', map_smul, SpanOmPf.isotropicSpan_orthogonal_anisotropicVector F' hy0, smul_zero, add_zero, add_zero] at this
      exact this
    obtain ⟨c, rfl⟩ := SpanOmPf.om_uniq F F' hD (by rw [← SpanOmPf.Xplus_eq]; exact hx) hxX
    have hzo : (VS D).hT F'.z ω = star Dd := by rw [SpanOmPf.hsw', SpanOmPf.omega_hermitian_z]
    have e3 : c * star Dd + β * -T' = 0 := by
      have := h3
      rw [map_add (f := _), map_add (f := _), map_smul, map_smul, hzo, SpanOmPf.z_orth_X F' hy', F'.z_norm, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have e4 : c * (-T * (Dr * star Dr)) + β * Dd = 0 := by
      have := h4
      rw [map_add (f := _), map_add (f := _), map_smul, map_smul, SpanOmPf.om_om, SpanOmPf.om_X' F F' hy', SpanOmPf.omega_hermitian_z, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have hc : c = 0 := by
      have hcG : c * (Dd * star Dd - T * T' * (Dr * star Dr)) = 0 := by
        linear_combination Dd * e3 + T' * e4
      exact (mul_eq_zero.1 hcG).resolve_right hG'
    have hβ : β = 0 := by
      rw [hc] at e4
      have : β * Dd = 0 := by linear_combination e4
      exact (mul_eq_zero.1 this).resolve_right hD
    rw [hc, hβ, zero_smul, zero_smul, add_zero, zero_add]
    exact hy'
  have hmU : m ∈ U := BwdNA.mem_of_orth_orth (VS D) U (fun u hu => by
    rw [SpanOmPf.hsw', (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm u (key u hu), star_zero])
  obtain ⟨y, hy, s, hs, rfl⟩ := Submodule.mem_sup.1 hmU
  obtain ⟨x', hx', w, hw, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hs
  exact ⟨x', hx', w, hw, a, b, by abel⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIE
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BetaI

theorem sub_add_eq {R W : Type*} [Ring R] [AddCommGroup W] [Module R W] {P : Submodule R W} {a b c : W}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (e : c = a + b) : (⟨c, hc⟩ : P) = ⟨a, ha⟩ + ⟨b, hb⟩ := by
  subst e; rfl

theorem sub_smul_eq {R W : Type*} [Ring R] [AddCommGroup W] [Module R W] {P : Submodule R W} {a c : W} (k : R)
    (ha : a ∈ P) (hc : c ∈ P) (e : c = k • a) : (⟨c, hc⟩ : P) = k • ⟨a, ha⟩ := by
  subst e; rfl

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
  (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
  (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V)

theorem sendsB_add {m₁ m₂ : (VS D).V}
    (h₁ : baseChange₂ D p m₁ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (h₂ : baseChange₂ D p m₂ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (k₁ : baseChange₂ D p (β₀ m₁) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (k₂ : baseChange₂ D p (β₀ m₂) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (s₁ : SendsB Zd p γ F'₂ ψ β₀ m₁) (s₂ : SendsB Zd p γ F'₂ ψ β₀ m₂) : SendsB Zd p γ F'₂ ψ β₀ (m₁ + m₂) := by
  intro hm hm₂
  have e1 : (⟨baseChange₂ D p (m₁ + m₂), hm⟩ : ↥((locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))) =
      ⟨baseChange₂ D p m₁, h₁⟩ + ⟨baseChange₂ D p m₂, h₂⟩ :=
    sub_add_eq h₁ h₂ hm ((baseChange₂ D p).map_add m₁ m₂)
  have e2 : (⟨baseChange₂ D p (β₀ (m₁ + m₂)), hm₂⟩ : ↥((locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))) =
      ⟨baseChange₂ D p (β₀ m₁), k₁⟩ + ⟨baseChange₂ D p (β₀ m₂), k₂⟩ :=
    sub_add_eq k₁ k₂ hm₂ (by rw [β₀.map_add, (baseChange₂ D p).map_add])
  have f1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (m₁ + m₂), hm⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m₁, h₁⟩ + (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m₂, h₂⟩ :=
    (congrArg _ e1).trans (LinearMap.map_add _ _ _)
  have f2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ (m₁ + m₂)), hm₂⟩ =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m₁), k₁⟩ +
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m₂), k₂⟩ :=
    (congrArg _ e2).trans (LinearMap.map_add _ _ _)
  exact ((congrArg ψ f1).trans (LinearEquiv.map_add ψ _ _)).trans
    ((congrArg₂ (· + ·) (s₁ h₁ k₁) (s₂ h₂ k₂)).trans f2.symm)

theorem sendsB_smul (c : D.host.E) {m : (VS D).V}
    (h₁ : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (k₁ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (s : SendsB Zd p γ F'₂ ψ β₀ m) : SendsB Zd p γ F'₂ ψ β₀ (c • m) := by
  intro hm hm₂
  have e1 : (⟨baseChange₂ D p (c • m), hm⟩ : ↥((locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))) =
      (D.s.atP p).ιE c • ⟨baseChange₂ D p m, h₁⟩ :=
    sub_smul_eq _ h₁ hm (Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂ p c m)
  have e2 : (⟨baseChange₂ D p (β₀ (c • m)), hm₂⟩ : ↥((locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))) =
      (D.s.atP p).ιE c • ⟨baseChange₂ D p (β₀ m), k₁⟩ :=
    sub_smul_eq _ k₁ hm₂ (by rw [LinearEquiv.map_smul]; exact Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂ p c (β₀ m))
  have f1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (c • m), hm⟩ =
      (D.s.atP p).ιE c • (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, h₁⟩ :=
    (congrArg _ e1).trans (LinearMap.map_smul _ _ _)
  have f2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ (c • m)), hm₂⟩ =
      (D.s.atP p).ιE c • (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), k₁⟩ :=
    (congrArg _ e2).trans (LinearMap.map_smul _ _ _)
  exact ((congrArg ψ f1).trans (LinearEquiv.map_smul ψ _ _)).trans
    ((congrArg ((D.s.atP p).ιE c • ·) (s h₁ k₁)).trans f2.symm)

theorem sendsB_X {m : (VS D).V} (hX1 : baseChange₂ D p m ∈ (locH Zd p).X (tLoc Zd p γ).f')
    (hX2 : baseChange₂ D p (β₀ m) ∈ (locH Zd p).X (locF' Zd p F'₂)) : SendsB Zd p γ F'₂ ψ β₀ m := by
  intro hm hm₂
  have e1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hX1
  have e2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hX2
  rw [e1, e2]
  exact LinearEquiv.map_zero ψ

theorem bcP_X_f' {x : (VS D).V} (hx : x ∈ Xsp (repF γ)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f' := by
  obtain ⟨h1, -⟩ := admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)
  set ξ := admXi D γ.lam (lf D F0) (repF γ) with hξdef
  have hξ : ξ⁻¹ * ξ = 1 := OmL.admissibility_witness_inv_mul γ.lam (lf D F0) (repF γ)
  have key : ∀ b, ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • frameAct (frame (repF γ)) ξ⁻¹ a = frame (repF γ) b := by
    intro b
    simp only [frameAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1' : ∀ c, ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) * ((ξ⁻¹ c a : 𝓞 D.host.E) : D.host.E) =
        (((ξ⁻¹ * ξ) c b : 𝓞 D.host.E) : D.host.E) := by
      intro c
      rw [Matrix.mul_apply]
      push_cast
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp only [← Finset.sum_smul, h1', hξ, Matrix.one_apply]
    simp
  change x ∈ Submodule.span D.host.E (Set.range (repF γ).fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← frame_csG, ← key, map_sum, Fin.sum_univ_castSucc]
    have hl : ξ (Fin.last D.R.rS) j.castSucc = 0 := h1 _ _ (Fin.castSucc_lt_last j)
    rw [hl]
    simp only [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (by simp)
    have e : baseChange₂ D p (frameAct (frame (repF γ)) ξ⁻¹ i.castSucc) =
        (((isUnit_sF' Zd p i.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • (tLoc Zd p γ).f' i.castSucc := by
      rw [tf', smul_smul]
      have : ((((isUnit_sF' Zd p i.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) *
          (TermLoc.sgnP' D p i.castSucc * frFac Zd.δ p i.castSucc) = 1 := (isUnit_sF' Zd p i.castSucc).val_inv_mul
      rw [this, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [(baseChange₂ D p).map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

end Place

section Place2

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
  (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
  (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V)

theorem z_orthG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') : G.fl.z ∈ orth (VS D) (Xsp G) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) G.fl.z x]
    have h := NMoveP.hT_f_X G.fl (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem X_le_orthG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') : Xsp G ≤ orth (VS D) (Xsp G) :=
  BwdNA.X_le_orth (VS D) (Xsp G) fun _ hx _ hy => NMoveP.hT_X_X G.fl hx hy

theorem starLast_sub_mem :
    frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ (Fin.last D.R.rS) - (repF γ).fl.z ∈
      Xsp (repF γ) := by
  obtain ⟨-, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  show ∑ a, (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) • frame (repF γ) a -
    (repF γ).fl.z ∈ Xsp (repF γ)
  rw [Fin.sum_univ_castSucc, hξ2, frame_lastG, (by simp : ((1 : 𝓞 D.host.E) : D.host.E) = 1), one_smul,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  rw [frame_csG]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem sends_beta_z
    (hS : (locH Zd p).SendsTo ψ.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last D.R.rS)) (locF' Zd p F'₂ (Fin.last D.R.rS)))
    (hzβ : β₀ (repF γ).fl.z = F'₂.fl.z) : SendsB Zd p γ F'₂ ψ β₀ (repF γ).fl.z := by
  intro hm hm₂
  obtain ⟨g, hg⟩ : ∃ g, g = frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ (Fin.last D.R.rS) :=
    ⟨_, rfl⟩
  have hd : g - (repF γ).fl.z ∈ Xsp (repF γ) := hg ▸ starLast_sub_mem γ
  have hlast : (tLoc Zd p γ).f' (Fin.last D.R.rS) = baseChange₂ D p g := by
    rw [tf', hg]
    have h1 : TermLoc.sgnP' D p (Fin.last D.R.rS) * frFac Zd.δ p (Fin.last D.R.rS) = 1 := sF'_last Zd p
    rw [h1, one_smul]
  have hgo : g ∈ orth (VS D) (Xsp (repF γ)) := by
    have e : g = (repF γ).fl.z + (g - (repF γ).fl.z) := by abel
    rw [e]
    exact add_mem (z_orthG (repF γ)) (X_le_orthG (repF γ) hd)
  have hmem : (tLoc Zd p γ).f' (Fin.last D.R.rS) ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') :=
    hlast ▸ bcP_perp_f' Zd p γ hgo
  have h2 : baseChange₂ D p (β₀ (repF γ).fl.z) = locF' Zd p F'₂ (Fin.last D.R.rS) := by
    rw [hzβ, locF'_last]
  have h3 : (1 : (D.s.atP p).Ep) • ψ.toLinearMap ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hmem⟩) =
      (1 : (D.s.atP p).Ep) • (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ :=
    hS ⟨(tLoc Zd p γ).f' (Fin.last D.R.rS), hmem⟩ ⟨baseChange₂ D p (β₀ (repF γ).fl.z), hm₂⟩ rfl h2
  have h3' := ((one_smul _ _).symm.trans h3).trans (one_smul _ _)
  have hX : baseChange₂ D p (repF γ).fl.z - (tLoc Zd p γ).f' (Fin.last D.R.rS) ∈ (locH Zd p).X (tLoc Zd p γ).f' := by
    rw [hlast, ← (baseChange₂ D p).map_sub]
    have : (repF γ).fl.z - g = -(g - (repF γ).fl.z) := by abel
    rw [this]
    exact bcP_X_f' Zd p γ ((Xsp (repF γ)).neg_mem hd)
  have h4 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (repF γ).fl.z, hm⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hmem⟩ := (Submodule.Quotient.eq _).2 hX
  exact (congrArg ψ h4).trans h3'

end Place2

end BetaI

theorem pinB_of (hSp : SpanOm D) (hOm : PinOm Zd u u' F0 what₂) (hW0 : PartialIsometryExtension Zd u u' F0 what₂) :
    PinB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hm hm₂ hmo
  have hB0 := hB
  obtain ⟨-, hZ, hSt, -, -, -, -, hG⟩ := hB
  obtain ⟨-, hZ₁d, -⟩ := starMinors_holds u u' F0 what₂ γ Z hZ
  have hl1 := star_frame_lead_minor γ (D.R.rS + 1)
  rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full] at hl1
  have hdet1 : (Zhat F0 (repF γ).fl).det ≠ 0 := fun h0 => hZ₁d (hl1.trans h0)
  have hzβ : β₀ (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hXmap := BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have horth : ∀ y ∈ orth (VS D) (Xsp (repF γ)), β₀ y ∈ orth (VS D) (Xsp (liftF F'₂)) := by
    intro y hy
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]
    exact Submodule.mem_map_of_mem hy
  have hmapX : ∀ x ∈ Xsp (repF γ), β₀ x ∈ Xsp (liftF F'₂) := fun x hx => by
    rw [← hXmap]; exact Submodule.mem_map_of_mem hx
  have k1 : ∀ y, y ∈ orth (VS D) (Xsp (repF γ)) →
      baseChange₂ D p y ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') := fun y hy => bcP_perp_f' Zd p γ hy
  have k2 : ∀ y, y ∈ orth (VS D) (Xsp (repF γ)) →
      baseChange₂ D p (β₀ y) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    fun y hy => baseChangeAt_perp' Zd p F'₂ (horth y hy)
  have hsp := hSp F0 (repF γ).fl hdet1 hG m hmo
  refine Exists.elim hsp fun x' h1 => ?_
  refine Exists.elim h1.2 fun w h2 => ?_
  refine Exists.elim h2.2 fun a h3 => ?_
  refine Exists.elim h3 fun b hmeq => ?_
  have hx' : x' ∈ (repF γ).fl.X := h1.1
  have hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus) := h2.1
  subst hmeq
  have ox : x' ∈ orth (VS D) (Xsp (repF γ)) := X_le_orthG (repF γ) hx'
  have hXle : (repF γ).fl.X ≤ F0.Xplus ⊔ (repF γ).fl.Xplus :=
    (show (repF γ).fl.X ≤ (repF γ).fl.Xplus from le_sup_left).trans le_sup_right
  have ow : w ∈ orth (VS D) (Xsp (repF γ)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx =>
    (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw x (hXle hx)
  have oz : (repF γ).fl.z ∈ orth (VS D) (Xsp (repF γ)) := z_orthG (repF γ)
  have oo : Gom F0.fvec (repF γ).fl.fvec ∈ orth (VS D) (Xsp (repF γ)) := BwdBetaCut.Gom_orth (lf D F0) (repF γ)
  have sx : SendsB Zd p γ F'₂ (φ' p) β₀ x' :=
    sendsB_X Zd p γ F'₂ (φ' p) β₀ (bcP_X_f' Zd p γ hx') (bcP_X' Zd p F'₂ (hmapX x' hx'))
  have sw : SendsB Zd p γ F'₂ (φ' p) β₀ w := hW0 γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p w hw
  have sz : SendsB Zd p γ F'₂ (φ' p) β₀ (repF γ).fl.z :=
    sends_beta_z Zd p γ F'₂ (φ' p) β₀ (hSt.2.1 p).2.2.2.2.2 hzβ
  have so : SendsB Zd p γ F'₂ (φ' p) β₀ (Gom F0.fvec (repF γ).fl.fvec) := hOm γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p
  have oxw := add_mem ox ow
  have oaz := Submodule.smul_mem _ a oz
  have obo := Submodule.smul_mem _ b oo
  have s1 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ ox) (k1 _ ow) (k2 _ ox) (k2 _ ow) sx sw
  have s2 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ oxw) (k1 _ oaz) (k2 _ oxw) (k2 _ oaz) s1
    (sendsB_smul Zd p γ F'₂ (φ' p) β₀ a (k1 _ oz) (k2 _ oz) sz)
  have s3 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ (add_mem oxw oaz)) (k1 _ obo) (k2 _ (add_mem oxw oaz))
    (k2 _ obo) s2 (sendsB_smul Zd p γ F'₂ (φ' p) β₀ b (k1 _ oo) (k2 _ oo) so)
  exact s3 hm hm₂

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarPinOm
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem pinOm_cancel {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {a k d₁ d₂ : R} {A B C : W}
    (ha : IsUnit a) (hk : IsUnit k) (hd : IsUnit d₂) (h1 : (a * d₂ * k) • A = (a * d₁ * k) • B)
    (h2 : d₂ • C = d₁ • B) : A = C := by
  have key : (a * d₂ * k) • A = (a * d₂ * k) • C := by
    rw [h1]
    calc (a * d₁ * k) • B = (a * k) • (d₁ • B) := by rw [smul_smul]; congr 1; ring
      _ = (a * k) • (d₂ • C) := by rw [h2]
      _ = (a * d₂ * k) • C := by rw [smul_smul]; congr 1; ring
  obtain ⟨v, hv⟩ := (ha.mul hd).mul hk
  have := congrArg (fun w => ((v⁻¹ : Rˣ) : R) • w) key
  simp only [← hv, smul_smul, Units.inv_mul, one_smul] at this
  exact this


set_option maxHeartbeats 4000000 in
theorem pinOm_holds : PinOm Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ hfr hW hO p hm hm₂
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, -, -⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hT2 := hS.2.1 p
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨K, hK⟩ : ∃ K : (D.s.atP p).Ep, K = (Zd.M p).L.cj (∏ j ∈ Finset.univ.erase (Fin.last D.R.rS), sF' Zd p j) *
      ∏ j, sF Zd p j := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (D.s.atP p).Ep, P = (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i)) := ⟨_, rfl⟩
  have ho1 : (locH Zd p).om (tLoc Zd p γ).f (tLoc Zd p γ).f' = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame (repF γ))) := by
    have e := om_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p)
    rw [Gom_frameAct (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hK] at e
    exact e
  have ho2 : (locH Zd p).om (tLoc Zd p γ).f (locF' Zd p F'₂) = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) := by
    have e := om_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p)
    rw [← hK] at e
    exact e
  have hd1 : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [GDl_frameAct_top (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hP] at e
    exact e
  have hd2 : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [← hP] at e
    exact e
  have hid := hT2.2.2.2.1
  have hs := hid.2.2.2.2.1
  dsimp only at hs
  rw [ho1, ho2, hd1, hd2] at hs
  have hω₂ : baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    baseChangeAt_perp' Zd p F'₂ (Gom_orth (lf D F0) F'₂)
  have h1 := hs (K • ⟨_, hm⟩) (K • ⟨_, hω₂⟩) rfl rfl
  have e1 := ((locH Zd p).mkW (tLoc Zd p γ).f').map_smul K ⟨_, hm⟩
  have e2 := ((locH Zd p).mkW (locF' Zd p F'₂)).map_smul K ⟨_, hω₂⟩
  have e3 := ((φ' p).toLinearMap).map_smul K ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hm⟩)
  rw [e1, e2, e3, smul_smul, smul_smul] at h1
  have hD2 : GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [GDl_top']
    have e : GZ (frame (lf D F0)) (frame F'₂) = Z := hS.1
    rw [e]; exact hZd
  have hOp : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        baseChange₂ D p (β₀ (Gom (frame (lf D F0)) (frame (repF γ)))) -
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).X (locF' Zd p F'₂) := by
    have := bcP_X' Zd p (liftF F'₂) hO
    rw [map_sub, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂] at this
    exact this
  have hcls : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ =
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hω₂⟩ := by
    rw [← LinearMap.map_smul, ← LinearMap.map_smul]
    apply (Submodule.Quotient.eq _).2
    exact hOp
  rw [map_mul, map_mul, cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)] at h1
  have hPu : IsUnit P := by
    rw [hP]
    exact (IsUnit.prod_univ_iff.2 fun i => (isUnit_sF Zd p _).map _).mul
      (IsUnit.prod_univ_iff.2 fun i => isUnit_sF' Zd p _)
  have hKu : IsUnit K := by
    rw [hK]
    exact ((IsUnit.prod_iff.2 fun j _ => isUnit_sF' Zd p j).map _).mul
      (IsUnit.prod_univ_iff.2 fun j => isUnit_sF Zd p j)
  have hDu : IsUnit ((D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)))) :=
    (isUnit_iff_ne_zero.2 (star_ne_zero.2 hD2)).map _
  exact pinOm_cancel (hPu.map _) hKu hDu h1 hcls

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem pinB_holds : PinB Zd u u' F0 what₂ :=
  pinB_of Zd (spanOm_holds D) (pinOm_holds Zd u u' F0 what₂) (localOrthogonal_holds Zd)

theorem betaInt_holds : BetaInt Zd u u' F0 what₂ :=
  betaInt_of Zd (lsetB_of Zd (pinB_holds Zd u u' F0 what₂)) (iotaB_of Zd (pinB_holds Zd u u' F0 what₂))

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
