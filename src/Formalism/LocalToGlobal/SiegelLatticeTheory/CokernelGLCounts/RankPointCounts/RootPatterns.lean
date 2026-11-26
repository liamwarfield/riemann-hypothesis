module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfConditions
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTyped
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RootPatterns

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.RealConjugatorData

variable {D : D7}

theorem blockIdx_loc (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) :
    ∀ (bs : List (D.host.E × ℕ)) (a i : ℕ), blockIdx (locBlocksFrom D ρ v a bs) i = Formalism.L2.SG.RealObj.blkOf bs i
  | [], _, _ => rfl
  | (t, s) :: bs, a, i => by
    simp only [locBlocksFrom, blockIdx, Formalism.L2.SG.RealObj.blkOf]
    split_ifs
    · rfl
    · rw [blockIdx_loc ρ v bs (a + s) (i - s), add_comm]

theorem mem_rootPat_iff (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (q : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :
    q ∈ rootPat (ptLoc D τ w) ↔ q.1 < q.2 ∧ Formalism.L2.SG.RealObj.blkOf w.1 q.1.1 = Formalism.L2.SG.RealObj.blkOf w.1 q.2.1 := by
  simp only [rootPat, ptLoc, ptLocS, locBlocks, Set.mem_setOf_eq, blockIdx_loc]
  simp [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ]

def idxF (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) : ↥(rootPat (ptLoc D τ w)) ≃ Formalism.L2.SG.RealObj.FreeE w where
  toFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).1 q.2⟩
  invFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).2 q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootCoords_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  unfold Formalism.MainNotions.S.rootCoords
  refine continuous_pi (fun q => ?_)
  unfold flagMat
  first
    | fun_prop
    | (simp only [Matrix.mul_apply, Matrix.of_apply]; fun_prop)
    | continuity
    | (exact ((continuous_apply _).comp (continuous_apply _)).comp
        (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const))

variable {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

theorem stCoordV_comp :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)) ∘
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ := by
  funext y q
  have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
  have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
      MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w) x q = x ((idxF τ w).symm q) :=
    fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp only [Function.comp_apply]
  rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
  unfold rootCoords flagMat
  rw [dite_eq_left (show ((idxF τ w).symm q).1.1.val < D.R.rS from ha), ← cMr_eq]
  rfl


include C in
theorem place (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    ∃ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (c : ℝ≥0∞),
      Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) μ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
        μ.map (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) =
          c • Measure.pi (fun _ : Formalism.L2.SG.RealObj.FreeE w => (volume : Measure ℂ)) := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  obtain ⟨μ₀, c, hHaar, hc0, hctop, hmap⟩ := hLoc D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW'
    (by rw [hTz']; exact hT u') (ptLoc D τ w) _ hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)
  have hemb := cMr_measEmb C γ τ
  set μ := Measure.comap (cMr C γ τ) μ₀ with hμ
  have hconc : μ₀ (Set.range (cMr C γ τ))ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) hHaar.2.2.1
    intro hR
    exact hx (rset_range C γ τ x hR)
  have hres : μ₀.restrict (Set.range (cMr C γ τ)) = μ₀ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hconc)
  have hmapc : μ.map (cMr C γ τ) = μ₀ := by rw [hμ, hemb.map_comap, hres]
  have : SigmaFinite μ₀ := hHaar.1
  refine ⟨μ, c, ⟨?_, ?_, ?_, fun s hs => ?_⟩, hc0, hctop, ?_⟩
  · exact SigmaFinite.of_map μ hemb.measurable.aemeasurable (by rw [hmapc]; infer_instance)
  · intro h0
    apply hHaar.2.1
    rw [← hmapc, h0, Measure.map_zero]
  · rw [hμ, hemb.comap_apply]
    refine measure_mono_null ?_ hHaar.2.2.1
    rintro _ ⟨y, hy, rfl⟩ hR
    exact hy ((stV_iff C γ τ u u' y).2 hR)
  · have hs0 := (stV_iff C γ τ u u' s).1 hs
    have hfun : cMr C γ τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (cMr C γ τ s) ∘ cMr C γ τ := by
      funext x
      obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
      show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat (s * x) * (uMat (γ (vOf X τ)) * C.Q τ) =
        (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ)) *
          (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat x * (uMat (γ (vOf X τ)) * C.Q τ))
      rw [show uMat (s * x) = uMat s * uMat x from rfl]
      calc C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * (uMat s * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ)
          = C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * ((uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) *
              (uMat (γ (vOf X τ)))⁻¹) * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ) := by
            rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.one_mul]
            simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hmeas_s : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => s * x) := measurable_const_mul s
    have hmeas_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (cMr C γ τ s)) := by
      refine Continuous.measurable ?_
      unfold Formalism.QuantumDeterminants.lmulM
      refine Continuous.matrix_mul continuous_const ?_
      exact continuous_id
    have key : (μ.map (fun x => s * x)).map (cMr C γ τ) = μ.map (cMr C γ τ) := by
      rw [Measure.map_map hemb.measurable hmeas_s, hfun, ← Measure.map_map hmeas_l hemb.measurable, hmapc]
      exact hHaar.2.2.2 _ hs0
    calc μ.map (fun x => s * x) = (((μ.map (fun x => s * x)).map (cMr C γ τ))).comap (cMr C γ τ) :=
          (hemb.comap_map _).symm
      _ = μ := by rw [key, hemb.comap_map]
  · rw [stCoordV_comp C u' w γ τ, ← Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable
      ((rootCoords_cont _ _ _ _).measurable.comp hemb.measurable),
      ← Measure.map_map (rootCoords_cont _ _ _ _).measurable hemb.measurable, hmapc, hmap, Measure.map_smul,
      (volume_measurePreserving_piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)).map_eq]
    · rfl
    · exact (MeasurableEquiv.piCongrLeft _ _).measurable.aemeasurable

theorem placeHaar_of_loc (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) : Formalism.L2.SG.NGPin.PlaceHaar := by
  intro D X u u' w γ hrep v
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  exact place C u u' w γ τ hLoc hrep

end Formalism.L2.SG.RootPatterns

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
namespace Formalism.L2.SG.Pf

theorem formRelC_holds : Formalism.L2.SG.Pf.FormRel.FormRelC :=
  formRelC_of (fun D X Y u u' => Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of X Y u u'
    (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')) Formalism.L2.SG.Pf.RelChar.relCharC_holds

theorem formNGC_holds : Formalism.L2.SG.NGVanish.FormNGC := formNGC_of_rel formRelC_holds

theorem formGC_holds : Formalism.L2.SG.Pf.MainEqVanish.FormGC := formGC_of_rel formRelC_holds

end Formalism.L2.SG.Pf
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc

namespace Formalism.L2.SG.RowsConc

theorem normExpSatTied_holds : NormExpSatTied := by
  intro D X Y u u' hT
  have hF := Formalism.L2.SG.Closed.FundExistsC_holds D X Y u u'
  have hO : ∀ w, Formalism.L2.SG.WuDecay.FoldOK X w Y.hK :=
    fun w => Formalism.L2.SG.Closed.FoldOKC_outright D X Y w hT.1 hT.2.2.2.2.1
  have hI := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u' (hO u) (hO u') hF
  have hAbs := absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright D X Y u u' hT
  exact Formalism.L2.SG.NormCut.normExpSatC'_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u u' hI
    (Formalism.L2.SG.Closed.AmpWellDefC_holds D X Y u u' hI) (Formalism.L2.SG.Closed.OOFundIndepC_holds D X Y u u' hF hI) hAbs

theorem idOneC_holds : IdOneC :=
  idOneC_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.IdCellDiagC_holds

end Formalism.L2.SG.RowsConc
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSIdx
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)

theorem comp_set_conjugated_level_eq : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
    (fun z => PIW.MassDataColumns.xuP X hb u p * z * (PIW.MassDataColumns.xuP X hb u p)⁻¹) '' MassDataIdxSteps.KppX X hb p := by
  unfold MassDataIdxSteps.KppX compSet K2u
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun y _ => ?_
  simp only [map_mul, map_inv]

theorem mem_compSet_iff (x : PIW.MassDataColumns.KvH X u p.1) :
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ↔
      x ∈ (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
  rw [PIW.MassDataColumns.mem_K2Hp_iff X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X) (Formalism.L2.SG.Closed.level_subgroup_properties X) u p x,
    comp_set_conjugated_level_eq]
  constructor
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx]
    simpa [mul_assoc] using hz
  · intro h
    exact ⟨_, h, by group⟩

theorem idxHp_eq : MassDataLevelSSteps.idxHp X hb u p = PIW.MassDataColumns.lIdxH X hb u p := by
  have hKv : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 ↔ y ∈ PIW.MassDataColumns.KvH X u p.1 :=
    fun y => Iff.rfl
  have hC2 : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = PIW.MassDataColumns.KvH X u p.1 := by
    have e : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = (PIW.MassDataColumns.KvH X u p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
      Set.ext hKv
    rw [e, Subgroup.closure_eq]
  have hS : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 →
      y ∈ PIW.MassDataColumns.KvH X u p.1 ∧ y ∈ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 := by
    intro y hy
    have hyK : y ∈ PIW.MassDataColumns.KvH X u p.1 :=
      (hKv y).1 ((level_compression_chain (X := X) (hb := hb) (p := p) u).2 hy)
    refine ⟨hyK, ?_⟩
    exact Subgroup.mem_subgroupOf.1 ((mem_compSet_iff X hb u p ⟨y, hyK⟩).1 hy)
  have hinf : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ⊓ PIW.MassDataColumns.KvH X u p.1 =
      PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 ⊓ PIW.MassDataColumns.KvH X u p.1 := by
    have hle : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≤ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 :=
      (Subgroup.closure_le _).2 fun y hy => (hS y hy).2
    refine le_antisymm (inf_le_inf_right _ hle) ?_
    rintro y ⟨hy2, hyK⟩
    refine ⟨Subgroup.subset_closure ?_, hyK⟩
    exact (mem_compSet_iff X hb u p ⟨y, hyK⟩).2 (Subgroup.mem_subgroupOf.2 hy2)
  have hsub : (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)))).subgroupOf
      (PIW.MassDataColumns.KvH X u p.1) =
      (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    have h1 := SetLike.ext_iff.1 hinf (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))
    simp only [Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.1 ⟨h, x.2⟩).1, fun h => (h1.2 ⟨h, x.2⟩).1⟩
  unfold MassDataLevelSSteps.idxHp PIW.MassDataColumns.lIdxH
  rw [hC2]
  exact congrArg Subgroup.index hsub

theorem sTypIdx_holds : STypIdx := by
  intro D X hb u p hT _
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have h1 := MassDataLevelSSteps.haarIdxLoc_holds X hb hK hT hL u p
  rw [MassDataLevelSSteps.locLevi_holds X hb hK hT hL u p, idxHp_eq X hb u p] at h1
  obtain ⟨ρ, hs, hk, hc⟩ := (PIW.MassDataColumns.locRedH_of_rest (PIW.MassDataColumns.locRedRest_of_models
    (PIW.MassDataColumns.hModelAll_of (PIW.MassDataColumns.hAdaptAll_of PIW.MassDataColumns.adapted_basis_every_place)
      PIW.MassDataColumns.level_clause_adapted_basis))) X hb hK u hT hL p
  rw [PIW.MassDataColumns.lIdxH_eq_of_red X hb u p ρ hs hk hc] at h1
  exact h1

theorem typedAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := typedAll_of_idx sTypIdx_holds

end Formalism.L2.SG.Pf.MassDataX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCV
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Finset

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ltSigma (r : ℕ) : LsNc5.LtPair r ≃ Σ a : Fin r, Fin a.val where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun q := ⟨(⟨q.2.val, lt_trans q.2.isLt q.1.isLt⟩, q.1), q.2.isLt⟩
  left_inv p := by rcases p with ⟨⟨b, a⟩, h⟩; rfl
  right_inv q := by rcases q with ⟨a, b⟩; rfl

theorem sum_lt (r : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p : LsNc5.LtPair r, g p.1.1.val p.1.2.val = ∑ a ∈ range r, ∑ b ∈ range a, g b a := by
  rw [Fintype.sum_equiv (ltSigma r) (fun p => g p.1.1.val p.1.2.val) (fun q => g q.2.val q.1.val) (fun _ => rfl),
    Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range a, g b a) r]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => g b a.val) a.val

theorem sum_id_real (a : ℕ) : ∑ b ∈ range a, (b : ℝ) = a * (a - 1) / 2 := by
  induction a with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem card_lt (r : ℕ) : (Fintype.card (LsNc5.LtPair r) : ℝ) = r * (r - 1) / 2 := by
  have h := sum_lt r (fun _ _ => 1)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h]
  exact sum_id_real r

theorem card_lt_nat (r : ℕ) : Fintype.card (LsNc5.LtPair r) = r * (r - 1) / 2 := by
  have h2 : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
  have : ((r * (r - 1) / 2 : ℕ) : ℝ) = r * (r - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · rw [h0]; simp
    · rw [Nat.cast_mul, Nat.cast_sub hp]; push_cast; ring
  exact_mod_cast (card_lt r).trans this.symm

theorem sumX (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * ((a : ℝ) - b)) =
    -((n - 1) * n * (2 * n - 1) / 6) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
    push_cast; ring

theorem sumK (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * (R - b) - 2 * (R - a)) =
    3 * ((n - 1) * n * (2 * n - 1) / 6) - 4 * R * (n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ∑ b ∈ range n, ((1 : ℝ) - 2 * (R - b) - 2 * (R - n)) =
        ∑ b ∈ range n, ((1 - 4 * R + 2 * (n : ℝ)) + 2 * (b : ℝ)) :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, sum_id_real]
    push_cast; ring

theorem sumR (R K : ℝ) (n : ℕ) : ∑ b ∈ range n, ((K + 1) * (1 - 2 * (R - b))) = (K + 1) * (n - 2 * R * n + n * (n - 1)) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem sumD (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ((1 / 2 : ℝ) - 2 * (R - a)) = n / 2 - 2 * R * n + n * (n - 1) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem prod_const_rpow {ι : Type*} (s : Finset ι) {c d : ℝ} (hd : 0 < d) (e : ι → ℝ) :
    ∏ x ∈ s, (c * d ^ e x) = c ^ s.card * d ^ (∑ x ∈ s, e x) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Real.rpow_sum_of_pos hd]

theorem half_succ (R : ℕ) : R * (R - 1) / 2 + R = R * (R + 1) / 2 := by
  rcases Nat.eq_zero_or_pos R with h0 | hp
  · subst h0; simp
  · obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (m + 1) * (m + 1 + 1) = (m + 1) * m + (m + 1) * 2 by ring,
      Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

theorem final_alg (t d : ℝ) (hd : 0 < d) (F R K : ℕ) (A B C E : ℝ)
    (h : A + B + C + E = LsNc5.covolumeExponent R K) :
    ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E) =
      t ^ (R * F) * (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) * d ^ LsNc5.covolumeExponent R K /
        (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
  have hd' : d ^ A * d ^ B * d ^ C * d ^ E = d ^ LsNc5.covolumeExponent R K := by
    rw [← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_add hd]
  have h2 : ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) =
      (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_eq_mul_inv, ← inv_pow, ← inv_pow, ← pow_add,
      ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← half_succ]
    congr 1
    ring
  calc ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E)
      = t ^ (R * F) * (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R *
          ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2)) * (d ^ A * d ^ B * d ^ C * d ^ E) := by ring
    _ = _ := by rw [h2, hd']; ring

theorem cVal_prod {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X := by
  have hd0 : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have hT : 0 < Tw (D := D) u := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos u
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [cVal]
  rw [prod_const_rpow _ hd0, prod_const_rpow _ hd0, prod_const_rpow _ hd0, ← Real.rpow_sum_of_pos hd0]
  have eX := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((a : ℝ) - b))
  have eK := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((D.R.rS : ℝ) - b) - 2 * ((D.R.rS : ℝ) - a))
  have eR : ∑ b : Fin D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ)))) =
      ∑ b ∈ range D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) :=
    Fin.sum_univ_eq_sum_range (fun b => ((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) D.R.rS
  have eD : ∑ a : Fin D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - (a : ℕ))) =
      ∑ a ∈ range D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) :=
    Fin.sum_univ_eq_sum_range (fun a => (1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) D.R.rS
  simp only [Finset.card_univ]
  rw [eX, eK, eR, eD, sumX, sumK, sumR, sumD, card_lt_nat, Fintype.card_fin]
  unfold LsNc5.covolN LsNc5.twoU
  exact final_alg _ _ hd0 _ _ _ _ _ _ _ (by unfold LsNc5.covolumeExponent; ring)

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOfCut
noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

theorem coordCovol_of_cut (hL : KapLaw) (hS : KapSurj) (hN : NOfib) (hB : BlockCovol)
    (hP : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X) :
    LsNc5.CoordCovol := by
  intro D X u FdN hF
  obtain ⟨hFm, hFex, hFu⟩ := hF
  obtain ⟨B, hBm, hBd, hB0, hlaw⟩ := hL X u
  obtain ⟨σ, hσm, hσ⟩ := hS X u
  obtain ⟨hNO, hNOmul, hNOinv, τ, hτ, hset⟩ := hN X u
  obtain ⟨-, hmulN, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  set NO := Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u
  have hinj : Set.InjOn (blk X u) (X.NinfU u) := fun s hs s' hs' h =>
    LsNc5.kapInj D X u hs hs' (by rw [kap_eq_Φc, kap_eq_Φc, h])
  set K' := blk X u '' (FdN ∩ X.NinfU u) with hK'def
  have hK'eq : K' = σ ⁻¹' FdN := by
    ext t; constructor
    · rintro ⟨s, ⟨hsF, hsN⟩, rfl⟩
      show σ (blk X u s) ∈ FdN
      rw [hinj (hσ _).1 hsN (hσ _).2]; exact hsF
    · intro ht; exact ⟨σ t, ⟨ht, (hσ t).1⟩, (hσ t).2⟩
  have hK'm : MeasurableSet K' := by rw [hK'eq]; exact hσm hFm

  have hmulB : ∀ δ ∈ X.NinfU u, ∀ g : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u δ) g = blk X u (δ * σ g) := by
    intro δ hδ g
    rw [hlaw δ hδ (σ g) (hσ g).1, (hσ g).2]
  have hinv : ∀ γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ p - τ p γ ∈ cLat X u p) →
      ∃ γ' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ' p - τ p γ' ∈ cLat X u p) ∧
        ∀ g, Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ g) = g ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' g) = g := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := (hset γ).2 hγ
    have hδN := hNO hδ
    have hδiN := hNO (hNOinv δ hδ)
    refine ⟨blk X u δ⁻¹, (hset _).1 ⟨δ⁻¹, hNOinv δ hδ, rfl⟩, fun g => ⟨?_, ?_⟩⟩
    · have hg := hσ g
      have hdg : δ * σ g ∈ X.NinfU u := (hmulN δ hδN (σ g) hg.1).1
      rw [hmulB δ hδN g, ← hlaw δ⁻¹ hδiN (δ * σ g) hdg, inv_mul_cancel_left, hg.2]
    · have hg := hσ g
      have hdg : δ⁻¹ * σ g ∈ X.NinfU u := (hmulN δ⁻¹ hδiN (σ g) hg.1).1
      rw [hmulB δ⁻¹ hδiN g, ← hlaw δ hδN (δ⁻¹ * σ g) hdg, mul_inv_cancel_left, hg.2]
  have hKd : ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, ∃! γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      (∀ p, γ p - τ p γ ∈ cLat X u p) ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ x ∈ K' := by
    intro x
    set g := σ x
    have hg := hσ x
    obtain ⟨δ, hδ, hδF⟩ := hFex g
    have hδN := hNO hδ
    refine ⟨blk X u δ, ⟨(hset _).1 ⟨δ, hδ, rfl⟩, ?_⟩, ?_⟩
    · rw [hmulB δ hδN x]
      exact ⟨δ * g, ⟨hδF, (hmulN δ hδN g hg.1).1⟩, rfl⟩
    · rintro γ' ⟨hγ', hγ'K⟩
      obtain ⟨δ', hδ', rfl⟩ := (hset γ').2 hγ'
      have hδ'N := hNO hδ'
      rw [hmulB δ' hδ'N x] at hγ'K
      obtain ⟨s, ⟨hsF, hsN⟩, hs⟩ := hγ'K
      have hs' : s = δ' * g := hinj hsN (hmulN δ' hδ'N g hg.1).1 hs
      have h1 : δ' * δ⁻¹ = 1 := hFu (δ * g) hδF (δ' * δ⁻¹) (hNOmul δ' hδ' δ⁻¹ (hNOinv δ hδ)) (by
        rw [show δ' * δ⁻¹ * (δ * g) = δ' * g by group, ← hs']; exact hsF)
      rw [mul_inv_eq_one.1 h1]
  have hfd : ∀ p, ∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F := fun p => (hB X u p).2.1
  choose F hF hFd using hfd
  have hcount : ∀ p, Countable (cLat X u p) := fun p => (hB X u p).1
  have hmain := Formalism.L2.SG.NGCut.SplitEmbedding.triFundT (CBlk D.R.rS) (CSpc (InfinitePlace X.B.I.F) D.R.k) (cMeas (InfinitePlace X.B.I.F) D.R.k)
    cHgt B hBm hBd hB0 τ hτ (cLat X u) hinv F hF hFd K' hK'm hKd
  have hvol : ∀ p, cMeas (InfinitePlace X.B.I.F) D.R.k p (F p) = ENNReal.ofReal (cVal X u p) :=
    fun p => (hB X u p).2.2 (F p) (hF p) (hFd p)
  have hcv : ∀ p, 0 ≤ cVal X u p := by
    intro p
    rcases p with ((p | b) | (p | a)) <;> simp only [cVal]
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · refine mul_nonneg (mul_nonneg ?_ (pow_nonneg (by norm_num) _)) (Real.rpow_nonneg (abs_nonneg _) _)
      exact pow_nonneg (show (0 : ℝ) ≤ Formalism.L2.SG.RealObj.Tw (D := D) u from Nat.cast_nonneg _) _
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · exact Real.rpow_nonneg (abs_nonneg _) _

  have himg : LsNc5.kap X u '' (FdN ∩ X.NinfU u) = Ψc ⁻¹' K' := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [kap_eq_Φc, Ψc_Φc]
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, hsy⟩
      refine ⟨s, hs, ?_⟩
      rw [kap_eq_Φc, hsy, Φc_Ψc]
  rw [himg]
  refine ⟨measurable_Ψc hK'm, ?_⟩
  rw [← map_Φc, Measure.map_apply measurable_Φc (measurable_Ψc hK'm)]
  have hpre : Φc ⁻¹' (Ψc ⁻¹' K') = K' := by
    ext x; simp only [Set.mem_preimage, Ψc_Φc]
  rw [hpre, hmain, Finset.prod_congr rfl fun p _ => hvol p, ← ENNReal.ofReal_prod_of_nonneg fun p _ => hcv p, hP]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem coordCovol_of (hL : KapLaw) (hN : NOfib) (hB : BlockCovol) : Formalism.L2.SG.Pf.LsNc5.CoordCovol :=
  coordCovol_of_cut hL kapSurj_holds hN hB (fun X u => cVal_prod X u)

end Formalism.L2.SG.Pf.NcReal.JX
end
