module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormExpSatHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LmatMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootCoordinatesIndex

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

theorem normExpDegC_of_leaves (hFL : Formalism.L2.SG.Pf.FinLeviC) (hOL : Formalism.L2.SG.Pf.OOLintSumC) : NormExpDegC :=
  normExpDegC_of hilbert_schmidt_blocks (Formalism.L2.SG.Closed.FoldOKC_holds hFL) (Formalism.L2.SG.Closed.OOIntAllC_holds hOL)
    (Formalism.L2.SG.Closed.AbsConvC_holds hOL) Formalism.L2.SG.Closed.AmpWellDefC_holds Formalism.L2.SG.Closed.OOFundIndepC_holds
    (fun _ X => chi_n_bilinear X) (fun D X Y u _ => Formalism.L2.SG.NormCut.colFreeAll D X Y u)
    (fun D X Y u _ h1 h2 h3 =>
      Formalism.L2.SG.NormCut.degLeftAct_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u h1 h2 h3)
    (fun D X Y u _ h1 h2 h3 => Formalism.L2.SG.NormCut.degRightAct_holds D X Y u h1 h2 h3)

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem haar_toReal_pos {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] {U S K : Set G} (hU : IsOpen U) (hne : U.Nonempty) (h1 : U ⊆ S) (h2 : S ⊆ K)
    (hK : IsCompact K) : 0 < (μ S).toReal :=
  ENNReal.toReal_pos ((lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono h1)).ne')
    (ne_top_of_le_ne_top (hK.measure_lt_top (μ := μ)).ne (measure_mono h2))

theorem haar_toReal_pos' {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    (hμ : μ.IsHaarMeasure) {U S K : Set G} (hU : IsOpen U) (hne : U.Nonempty) (h1 : U ⊆ S) (h2 : S ⊆ K)
    (hK : IsCompact K) : 0 < (μ S).toReal := by
  haveI := hμ
  exact haar_toReal_pos μ hU hne h1 h2 hK

section Typed

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X)

theorem kg_sub_kv : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KvX X p := by
  intro x hx
  simp only [MassDataIdxSteps.KgX, MassDataIdxSteps.KvX] at hx ⊢
  exact hx.1

theorem kv_facts : IsOpen (MassDataIdxSteps.KvX X p) ∧ IsCompact (MassDataIdxSteps.KvX X p) ∧
    IsOpen (MassDataIdxSteps.KgX X p) ∧ (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KgX X p := by
  obtain ⟨K, hK, ho, hc, hg⟩ := stK_holds X p
  obtain ⟨ρ, -, hρ⟩ := stRed_holds X p K hK
  refine ⟨by rw [← hK]; exact ho, by rw [← hK]; exact hc, hg, ?_⟩
  have h1 := (hρ 1).mp (map_one ρ)
  simpa using h1

theorem kg_sub_kpp : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KppX X hb p := by
  intro x hx
  obtain ⟨K, hK, -⟩ := stK_holds X p
  obtain ⟨ρ, hs, hρ⟩ := stRed_holds X p K hK
  obtain ⟨A, hA, hker, -⟩ := stImA_holds X hb p K hK ρ hs hρ
  have hxK : x ∈ (K : Set (MassDataIdxSteps.HAp X p)) := by
    rw [hK]
    exact kg_sub_kv X p hx
  rw [← hA]
  exact ⟨⟨x, hxK⟩, hker (MonoidHom.mem_ker.mpr ((hρ ⟨x, hxK⟩).mpr hx)), rfl⟩

theorem kpp_sub_kv : MassDataIdxSteps.KppX X hb p ⊆ MassDataIdxSteps.KvX X p := by
  obtain ⟨K, hK, -⟩ := stK_holds X p
  obtain ⟨ρ, hs, hρ⟩ := stRed_holds X p K hK
  obtain ⟨A, hA, -⟩ := stImA_holds X hb p K hK ρ hs hρ
  intro x hx
  rw [← hA] at hx
  obtain ⟨y, -, rfl⟩ := hx
  rw [← hK]
  exact y.2

theorem kg_sub_knat (u : D.what₂.Word) : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KnatX X u p := by
  intro y hy
  have h1 : (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KvX X p := kg_sub_kv X p (kv_facts X p).2.2.2
  exact ⟨hy.1, 1, y, (Ssub _ _ _ _).one_mem, h1, hy, (one_mul y).symm⟩

theorem knat_sub_kv (u : D.what₂.Word) : MassDataIdxSteps.KnatX X u p ⊆ MassDataIdxSteps.KvX X p := fun _ h => h.1

end Typed

section Typed2

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X)


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures in
theorem level_compression_chain (u : D.what₂.Word) :
    MassDataIdxSteps.KgX X p ⊆ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ∧
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ⊆ MassDataIdxSteps.KvX X p := by
  obtain ⟨K, hK, -, -, -⟩ := MassDataIdxSteps.stK_holds X p
  obtain ⟨ρ, -, hker⟩ := stRed_holds X p K hK
  have hKf := (PIW.MassDataColumns.finHA_mem_Kf_iff X hb (X.xu u)).2 (X.xu_K u)
  rw [Kf, Subgroup.mem_iInf] at hKf
  have haK : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) ∈ MassDataIdxSteps.KvX X p := hKf p.1
  have hcs : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
      (fun z => haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) * z *
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)))⁻¹) ''
        MassDataIdxSteps.KppX X hb p := by
    unfold compSet K2u MassDataIdxSteps.KppX compSet
    rw [Set.image_image, Set.image_image]
    congr 1
    funext y
    rw [map_mul, map_mul, map_inv]
  rw [hcs]
  generalize haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) = a at haK ⊢
  have haK' : a ∈ (K : Set (MassDataIdxSteps.HAp X p)) := by rw [hK]; exact haK
  constructor
  · intro k hk
    have hkK : k ∈ (K : Set (MassDataIdxSteps.HAp X p)) := hK ▸ kg_sub_kv X p hk
    have h2 := (hker ((⟨a, haK'⟩ : K)⁻¹ * ⟨k, hkK⟩ * ⟨a, haK'⟩)).1
      (by rw [map_mul, map_mul, (hker ⟨k, hkK⟩).2 hk, mul_one, map_inv, inv_mul_cancel])
    have h2' : a⁻¹ * k * a ∈ MassDataIdxSteps.KgX X p := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
    refine ⟨a⁻¹ * k * a, kg_sub_kpp X hb p h2', ?_⟩
    group
  · rintro _ ⟨z, hz, rfl⟩
    have hzK : z ∈ (K : Set (MassDataIdxSteps.HAp X p)) := hK ▸ kpp_sub_kv X hb p hz
    rw [← hK]
    exact K.mul_mem (K.mul_mem haK' hzK) (K.inv_mem haK')

end Typed2

section Glob

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem conjugated_level_open_one_mem (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) : IsOpen (K2u X hb u) ∧ (1 : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u ∧
    K2u X hb u ⊆ (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := PIW.MassDataColumns.isTopGroup_HA (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.sig X.B.I.J
  set e := Formalism.L2.SG.Pf.Meas.eFin X.B.I hb
  have h1 : IsOpen (levelUnitary X hb) := by
    have hk : levelUnitary X hb = e '' X.K2 := rfl
    rw [hk]
    exact e.toHomeomorph.isOpenMap _ (Formalism.L2.SG.Pf.level_subgroup_compact_open X).1
  set a := finHA X hb (X.xu u)
  have hc : K2u X hb u = ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)) '' levelUnitary X hb := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]
    exact ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)).isOpenMap _ h1
  · refine ⟨finHA X hb 1, ⟨1, hK.1, rfl⟩, ?_⟩
    show a * finHA X hb 1 * a⁻¹ = 1
    rw [finHA_eq_eFin, map_one, mul_one, mul_inv_cancel]
  · rintro _ ⟨y, ⟨k, hk2, rfl⟩, rfl⟩
    have hxu : a ∈ MassDataMassesW.KX X := (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)
    have hkK : finHA X hb k ∈ MassDataMassesW.KX X :=
      (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)
    exact (MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)

theorem closed_SNH_X (u : D.what₂.Word) :
    IsClosed (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      IsClosed (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      IsClosed (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact PI.LevelKSplit.W.ExC.closed_SNH (MassDataVolumesW.stepHerm X) (fun x => star_star x) (frameOf X u) _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u)

end Glob

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem sv_pos (w : D.what₂.Word) (p : TypX X) {S : Set (MassDataIdxSteps.HAp X p)}
    (h1 : MassDataIdxSteps.KgX X p ⊆ S) (h2 : S ⊆ MassDataIdxSteps.KvX X p) :
    0 < ((X.measW w).μSv p.1 (Subtype.val ⁻¹' S)).toReal := by
  haveI := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  obtain ⟨-, hc, hgo, h1g⟩ := kv_facts X p
  have hcl := MassDataLevelSSteps.LatTop.isClosed_Ssub (v := p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)
  exact haar_toReal_pos _ (hgo.preimage continuous_subtype_val)
    ⟨1, show (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KgX X p from h1g⟩
    (Set.preimage_mono h1) (Set.preimage_mono h2) (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc)

theorem gv_pos (p : TypX X) {S : Set (MassDataIdxSteps.HAp X p)}
    (h1 : MassDataIdxSteps.KgX X p ⊆ S) (h2 : S ⊆ MassDataIdxSteps.KvX X p) :
    0 < (X.measG.μGv p.1 S).toReal := by
  haveI := X.measG_norm.2.2.2.1 p.1
  obtain ⟨-, hc, hgo, h1g⟩ := kv_facts X p
  exact haar_toReal_pos _ hgo ⟨1, h1g⟩ h1 h2 hc

theorem locHaarPosC_holds : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hKc := kCompactOpen_holds X
  have hKcs : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Ssub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).1.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have hKcn : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Nsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).2.1.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have hKch : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Hsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).2.2.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have h1K : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    (MassDataMassesW.KX X).one_mem
  refine ⟨fun p => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gv_pos X p (kg_sub_kv X p) subset_rfl
  · exact gv_pos X p (kg_sub_knat X p u) (knat_sub_kv X p u)
  · exact gv_pos X p (kg_sub_kpp X hb p) (kpp_sub_kv X hb p)
  · exact sv_pos X u p (kg_sub_kv X p) subset_rfl
  · exact sv_pos X u' p (kg_sub_kv X p) subset_rfl
  · exact sv_pos X u p (level_compression_chain X hb p u).1 (level_compression_chain X hb p u).2
  · exact sv_pos X u' p (level_compression_chain X hb p u').1 (level_compression_chain X hb p u').2
  · haveI := X.measG_norm.2.2.1
    exact haar_toReal_pos _ hKc.2 ⟨1, h1K⟩ subset_rfl subset_rfl hKc.1
  · haveI := (X.measW_norm u).2.2.2.2.2.2.1
    exact haar_toReal_pos _ (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcs u)
  · haveI := (X.measW_norm u').2.2.2.2.2.2.1
    exact haar_toReal_pos _ (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcs u')
  · exact haar_toReal_pos' _ (X.measW_norm u).2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKch u)
  · exact haar_toReal_pos' _ (X.measW_norm u').2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKch u')
  · obtain ⟨ho, h1, hs⟩ := conjugated_level_open_one_mem X hb hK u
    exact haar_toReal_pos' _ (X.measW_norm u).2.2.1 (ho.preimage continuous_subtype_val) ⟨1, h1⟩ subset_rfl (Set.preimage_mono hs) (hKch u)
  · obtain ⟨ho, h1, hs⟩ := conjugated_level_open_one_mem X hb hK u'
    exact haar_toReal_pos' _ (X.measW_norm u').2.2.1 (ho.preimage continuous_subtype_val) ⟨1, h1⟩ subset_rfl (Set.preimage_mono hs) (hKch u')
  · exact haar_toReal_pos' _ (X.measW_norm u).2.2.2.2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcn u)
  · exact haar_toReal_pos' _ (X.measW_norm u').2.2.2.2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcn u')

end Main

end Formalism.L2.SG.Pf.MassDataX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerFix
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG2

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_low {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, a < b → lmat Z p g l ρ a b = 0) ∧ ∀ a, lmat Z p g l ρ a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hl0 a b h, hρ0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem corner_fix {L R C : Formalism.L2.SG.LsDatumB.MatP D p} (hL0 : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1)
    (hR0 : ∀ a b, b < a → R a b = 0) (hR1 : ∀ a, R a a = 1)
    (hC : ∀ a b, ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) → C a b = 0) : L * C * R = C := by
  have hLl : ∀ a, L a (Fin.last D.R.rS) = if a = Fin.last D.R.rS then 1 else 0 := by
    intro a
    split_ifs with h
    · subst h; exact hL1 _
    · exact hL0 a _ (lt_of_le_of_ne (Fin.le_last a) h)
  have hRl : ∀ b, R (Fin.last D.R.rS) b = if b = Fin.last D.R.rS then 1 else 0 := by
    intro b
    split_ifs with h
    · subst h; exact hR1 _
    · exact hR0 _ b (lt_of_le_of_ne (Fin.le_last b) h)
  ext a b
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last D.R.rS) (fun d _ hd => by
      rw [Finset.sum_eq_zero (fun c _ => by rw [hC c d (fun h => hd h.2), mul_zero]), zero_mul]) (by simp),
    Finset.sum_eq_single (Fin.last D.R.rS) (fun c _ hc => by rw [hC c _ (fun h => hc h.1), mul_zero]) (by simp),
    hLl a, hRl b]
  by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS
  · subst ha; subst hb; simp
  · rw [if_neg hb, mul_zero, hC a b (fun h => hb h.2)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]

end ModeG2

end Formalism.L2.SG.Pf.FibQ
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelPf
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRelPf

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  apply List.ext_get
  · simp [ofPts, toPts, Composition.length]
  · intro n h1 h2
    simp [ofPts, toPts, Composition.blocksFun]

theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  apply Subtype.ext
  rw [← ofPts_toPts p, ← ofPts_toPts q, h]

end Formalism.L2.SG.Pf.FormRelPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel Formalism.L2.SG.Pf.FormRelPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formRelC_of (hRD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.Pf.RowForm.RealDecompC X Y u u')
    (hRC : Formalism.L2.SG.Pf.RelCharC) : FormRelC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ ν hν t ht hv => ?_⟩
  have hG : t.G ≠ 0 := Formalism.L2.SG.Pf.RowForm.realDecomp_G_ne X Y u u' t ht
  have hrel : t.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨hpt, hall⟩ := hRD D X Y u u' t hrel hG
  refine ⟨⟨_, rfl, hpt⟩, fun w hw hwr => ?_⟩
  have hw' : w = Formalism.L2.SG.PairVal.ptOf t.toTerm := toPts_injective hw
  subst hw'
  have hγ := Formalism.L2.SG.Pf.RowForm.isPtRep_gamW X u u' hwr
  obtain ⟨g, hg, g', hg', hdec⟩ := hall _ hγ
  obtain ⟨c, hc⟩ := formTransp_any (X := X) (Y := Y) (u := u) (u' := u') (νq := ν) hν.2 hRC t hrel hwr g hg g' hg'
    hdec
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have := FiniteDimensional.complete ℂ (X.Vpi u')
  refine ⟨(c : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g')),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'), ?_⟩
  rw [hc, hdec, Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' (X.psiInfU u g) (X.psiInfU u' g')
    (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg) (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg')
    (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x), ← Complex.coe_smul, smul_smul]

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealConjugatorData
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RealConjugatorData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) :
    Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem uMat_inv' {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g⁻¹ = (uMat g)⁻¹ := by
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)⁻¹
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g * (uMat g)⁻¹ = 1 := by
  rw [← uMat_inv']
  show (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : (uMat g)⁻¹ * uMat g = 1 := by
  rw [← uMat_inv']
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

def cMr (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)

theorem cMr_eq (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    cMr C γ τ y = Formalism.L2.SG.RealFrameCoordinates.cMg C γ τ y := by
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) =
    C.Qi τ * ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) * C.Q τ
  simp only [Matrix.mul_assoc]

theorem cMr_closedEmb : Topology.IsClosedEmbedding (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  set g := uMat (γ (vOf X τ))
  have h1 : g * g⁻¹ = 1 := uMat_mul_inv _
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  let L : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ ≃ₜ
      Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
    { toFun := fun M => C.Qi τ * g⁻¹ * M * (g * C.Q τ)
      invFun := fun M => g * C.Q τ * M * (C.Qi τ * g⁻¹)
      left_inv := fun M => by
        show g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹) = M
        calc g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹)
            = g * (C.Q τ * C.Qi τ) * g⁻¹ * M * (g * (C.Q τ * C.Qi τ) * g⁻¹) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [hQQi, Matrix.mul_one, h1, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun M => by
        show C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ) = M
        calc C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ)
            = C.Qi τ * (g⁻¹ * g) * C.Q τ * M * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact L.isClosedEmbedding.comp ((Formalism.REAL.isClosedEmbeddingMatrix _ (X.B.I.ε (vOf X τ))).1)

theorem cMr_measEmb : MeasurableEmbedding (cMr C γ τ) := (cMr_closedEmb C γ τ).measurableEmbedding

variable (u u' : D.what₂.Word)

theorem conjugator_inverse : (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ =
    C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  refine Matrix.inv_eq_right_inv ?_
  show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = 1
  calc C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ)
      = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, hQiQ]

theorem stV_iff (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    y ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ) ↔
      cMr C γ τ y ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := y.2
  have hy' : (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)).2
  have h1 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u τ).1 _ hy
  have h2 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u' τ).1 _ hy'
  have e2 : C.Qi τ * uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) * C.Q τ = cMr C γ τ y := by
    rw [cMr_eq]
    unfold Formalism.L2.SG.RealFrameCoordinates.cMg
    rw [show uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = uMat ((γ (vOf X τ))⁻¹) * uMat y * uMat (γ (vOf X τ)) from rfl,
      uMat_inv']
  have e1 : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)) * Matrix.of (cMr C γ τ y) *
      (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ = C.Qi τ * uMat y * C.Q τ := by
    rw [conjugator_inverse]
    show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ)) *
      (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = C.Qi τ * uMat y * C.Q τ
    calc _ = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * uMat y *
          (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, Matrix.mul_one]
  show (Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat y) ∧ Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))) ↔ _
  rw [h1, h2, e2]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨hb, ?_⟩
    convert ha using 1
    exact e1
  · rintro ⟨hb, ha⟩
    refine ⟨?_, hb⟩
    convert ha using 1
    exact e1.symm

theorem rset_range (m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hm : Matrix.of m ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ)) :
    m ∈ Set.range (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := C.isT τ
  have hmU : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm.1.1
  have hgi0 : (uMat (γ (vOf X τ))⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat (γ (vOf X τ))⁻¹ =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹).2
  rw [uMat_inv'] at hgi0
  set g := uMat (γ (vOf X τ))
  have hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := (γ (vOf X τ)).2
  have hgi : (g⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g⁻¹ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := hgi0
  have hQi : (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    rw [← hH]
    calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
        = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  set M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ := g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹ with hM
  have hMU : Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M
        = (g⁻¹)ᴴ * ((C.Qi τ)ᴴ * ((Matrix.of m)ᴴ * ((C.Q τ)ᴴ *
            (gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g) * C.Q τ) * Matrix.of m) * C.Qi τ) * g⁻¹ := by
          rw [hM]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hg, hH, hmU, hQi, hgi]
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  refine ⟨toUJn M hMU, ?_⟩
  show C.Qi τ * g⁻¹ * M * (g * C.Q τ) = Matrix.of m
  rw [hM]
  calc C.Qi τ * g⁻¹ * (g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹) * (g * C.Q τ)
      = (C.Qi τ * (g⁻¹ * g) * C.Q τ) * Matrix.of m * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of m := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]

end Formalism.L2.SG.RealConjugatorData

end
end
