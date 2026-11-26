module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MassDataPosAllOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DvPosC

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
namespace Formalism.L2.SG.NGPin

theorem locRootHaar_holds : LocRootHaar :=
  fun k r hk z z' h1 h2 h3 h4 p g₀ hg hZ => Formalism.L2.SG.Pf.RootHaarLoc.locRootHaar k r hk z z' h1 h2 h3 h4 p g₀ hg hZ

theorem placeHaar_holds : PlaceHaar := Formalism.L2.SG.RootPatterns.placeHaar_of_loc locRootHaar_holds

theorem stepPinExists : Formalism.L2.SG.NGAnalytic.StepPinExists := stepPinExists_of_place placeHaar_holds

end Formalism.L2.SG.NGPin
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLoUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hc | hc
    · rw [(h a c).1 hc, zero_mul]
    · rw [(h' c b).1 (lt_of_le_of_lt hc hab), mul_zero]
  · subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(h a a).2 rfl, (h' a a).2 rfl, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc' | hc'
      · rw [(h' c a).1 hc', mul_zero]
      · rw [(h a c).1 hc', zero_mul]
    · simp

theorem isUpUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first | exact GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul .. | (apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h h' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R

theorem isLoUni_one : IsLoUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne, fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isUpUni_one : IsUpUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isLoUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) : IsLoUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_lo (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [hb hc', mul_zero]
    · rw [(h a c).1 hc', zero_mul]
  · simp

theorem isUpUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) : IsUpUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_up (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [(h a c).1 hc', zero_mul]
    · rw [hb hc', mul_zero]
  · simp

end Uni

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def stZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) : Subgroup (Formalism.L2.SG.PairVal.GLR D) where
  carrier := stZSet M δ u u' Z L
  one_mem' := by
    refine ⟨1, ?_, isLoUni_one, 1, isUpUni_one, by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z' => ?_⟩⟩
    · simp [Matrix.nonsing_inv_mul L hL]
    · simp [zhatOM_zhatOM]
  mul_mem' := by
    rintro x y ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩ ⟨y', hy, hyl, by', hby, hyZ, hyp⟩
    refine ⟨x' * y', ?_, ?_, by' * bx, isUpUni_mul hby hbx, ?_, fun p => ?_⟩
    · rw [Units.val_mul, hx, hy, Units.val_mul]
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L * (L⁻¹ * (y' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) * (y' : Formalism.L2.SG.PairVal.MatR D) * L := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv L hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    · rw [Units.val_mul]
      exact isLoUni_mul hxl hyl
    · rw [Units.val_mul]
      calc (x' : Formalism.L2.SG.PairVal.MatR D) * (y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) * ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * by') * bx := by
            simp only [Matrix.mul_assoc]
        _ = ZhatOM Z := by rw [hyZ, hxZ]
    · obtain ⟨l1, ρ1, hl1, hρ1, h1⟩ := hxp p
      obtain ⟨l2, ρ2, hl2, hρ2, h2⟩ := hyp p
      refine ⟨l1 * l2, ρ2 * ρ1, intLow_mul _ hl1 hl2, intUp_mul _ hρ2 hρ1, fun Z' => ?_⟩
      have e : ((x' * y' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) *
            ZhatOM (ZhatOM ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * by')) * bx := by
        rw [zhatOM_zhatOM, Units.val_mul]
        simp only [Matrix.mul_assoc]
      rw [e, h1, h2]
      simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩
    obtain ⟨hxi, hxi1, hxi2⟩ := isLoUni_inv hxl
    obtain ⟨hbi, hbi1, hbi2⟩ := isUpUni_inv hbx
    have hZ : ((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx⁻¹ = ZhatOM Z := by
      rw [Matrix.coe_units_inv]
      calc (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ZhatOM Z * bx⁻¹ =
          (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx) * bx⁻¹ := by rw [hxZ]
        _ = ZhatOM Z := by
          simp only [← Matrix.mul_assoc]
          rw [hxi1, Matrix.one_mul, Matrix.mul_assoc, hbi2, Matrix.mul_one]
    refine ⟨x'⁻¹, ?_, by rw [Matrix.coe_units_inv]; exact hxi, bx⁻¹, hbi, hZ, fun p => ?_⟩
    · rw [Matrix.coe_units_inv, Matrix.coe_units_inv, hx]
      have hLi := Matrix.nonsing_inv_mul L hL
      have hiL := Matrix.mul_nonsing_inv L hL
      refine Matrix.inv_eq_left_inv ?_
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * L * (L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * (L * L⁻¹) * (x' : Formalism.L2.SG.PairVal.MatR D)) * L := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hiL, Matrix.mul_one, hxi1, Matrix.mul_one, hLi]
    · obtain ⟨l, ρ, hl, hρ, h⟩ := hxp p
      obtain ⟨hli, hli1, hli2⟩ := intLow_inv _ hl
      obtain ⟨hρi, hρi1, hρi2⟩ := intUp_inv _ hρ
      refine ⟨l⁻¹, ρ⁻¹, hli, hρi, fun Z' => ?_⟩
      have h2 := h (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹))
      have e : (x' : Formalism.L2.SG.PairVal.MatR D) *
          ZhatOM (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹)) * bx =
          ZhatOM Z' := by
        rw [zhatOM_zhatOM, Matrix.coe_units_inv]
        simp only [← Matrix.mul_assoc]
        rw [hxi2, Matrix.one_mul, Matrix.mul_assoc, hbi1, Matrix.mul_one]
      rw [e, zhatOM_zhatOM] at h2
      rw [h2]
      simp only [← Matrix.mul_assoc]
      rw [hli1, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hρi2, Matrix.mul_one]

theorem mem_CZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) (a : Formalism.L2.SG.PairVal.GLR D) :
    a ∈ CZ M δ u u' Z L ↔ a ∈ stZSet M δ u u' Z L := by
  have e : CZ M δ u u' Z L = stZ M δ u u' Z L hL := by
    unfold CZ
    exact Subgroup.closure_eq (stZ M δ u u' Z L hL)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolGrp

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTied
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXFrameVol
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem three_dvd_cubic (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by

  obtain ⟨k, hk | hk | hk⟩ : ∃ k, r = 3 * k ∨ r = 3 * k + 1 ∨ r = 3 * k + 2 := ⟨r / 3, by omega⟩
  · subst hk
    exact ⟨(3 * k + 1) * (6 * k + 1) * (4 * k + 1), by ring⟩
  · subst hk
    exact ⟨(3 * k + 2) * (2 * k + 1) * (12 * k + 7), by ring⟩
  · subst hk
    exact ⟨(k + 1) * (8 * (3 * k + 2) ^ 2 + 10 * (3 * k + 2) + 3), by ring⟩

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem frameVolAt_of (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) (hP : ProdConv X u u' ψ) :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq := by
  have hMS := Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds X u u' ψ hψ hstd hP
  have hZZ : 0 < (locOf X u u' ψ).volZZ := hP.2.2.2.2.2.2.1
  unfold Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt
  show ((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) / (locOf X u u' ψ).volZZ = _
  unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.LemmaMS at hMS
  rw [hMS, mul_div_assoc, div_self hZZ.ne', mul_one]
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  have he : (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) =
      ((D.R.f * Formalism.L2.SG.Pf.Carrier.EnergyConst.e1 D : ℕ) : ℝ) := by
    unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.e1
    obtain ⟨c, hc⟩ := three_dvd_cubic D.R.rS
    rw [mul_assoc, hc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    push_cast
    ring
  have hg : (X.B.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by rw [X.g_eq]; simp [Formalism.MainNotions.S.Lat.gS]
  rw [hv, he, Real.rpow_natCast, hg, mul_assoc D.R.f]

end Formalism.L2.SG.Pf.MassDataX
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol
  Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nTy_holds : OnTied fun D X hb Y u u' X0 ψ =>
    Formalism.L2.SG.MassDataConc.InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
      (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro _ _ _ _ _ _ _ _ D _ X Y u u' _ hb X0 ψ hT
  exact inTypedC_loc X hb Y.hK _ _ u u' X0 ψ _ 0 0 1 _ _ _ _ _ _ _
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hT.2.1 hT.2.2.1

theorem frameVolAt_of_prodConv (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) : OnTied fun D X hb Y u u' X0 ψ =>
    FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
      (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  exact frameVolAt_of X hb Y u u' X0 ψ 0 0 1 _ _ _ _ _ hT.2.1 hT.2.2.1
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT)

theorem nPos_of (hSW : PI.VolStabS.MassDataS.SWXS) (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) :
    OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' :=
    ⟨hT.1, hCtx.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1
    (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)
    (locHaarPosC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _)
    (covolPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hSW hT.2.1 hT.2.2.2.1
      hT.1 hT.2.2.2.2.2.2)
    (Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hK2 hV)
    (recPosC_of_dv X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _
      (fun X v => dvPosC_holds X v) hH)
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT) (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u')
    (Formalism.L2.SG.WConst.kapN_pos (D := D)) le_rfl le_rfl one_pos

end Formalism.L2.SG.Pf.MassDataX
end
end
