module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInvT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnimodInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal) (h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
      ∫⁻ g, f (g * h) ∂X.measG.μGinf = ∫⁻ g, f g ∂X.measG.μGinf

def WittNear : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a Ω' a₂, IsChart X u' hT Ω a → IsChart X u' hT Ω' a₂ →
    ∀ T ∈ Ω ∩ Ω', IsUnit (a₂ T) → ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')

def GoodChartEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω' a₂, IsChart X u' hT Ω' a₂ ∧ GoodP X u' hT μinf νinf a₂

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperW
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem fbI_closed {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) : IsClosed (FbI X u' hT) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det =
      inclR (F := X.B.I.F) (Ainf X.B.I.F) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det := by
    rw [RingHom.map_det]; rfl
  have hsub : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} ⊆ IndI X := by
    intro y hy
    have hy' : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y = ((TI X u' hT : HmI X) : Matrix _ _ _) := hy
    apply linIndep_of_isUnit_det (R := Ainf X.B.I.F) (σ := X.B.I.cm.sig) (J := X.B.I.J) y
    rw [hy']
    show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det
    rw [hdet]
    exact (isUnit_iff_ne_zero.2 hd).map _
  have he : FbI X u' hT = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} :=
    Set.inter_eq_left.2 hsub
  rw [he]
  exact isClosed_singleton.preimage (continuous_gramI X)

theorem properOne_of (hW : WittInf) (hH : MassDataMassesW.HinfCompact) : ProperOne := by
  intro D X u' ψ hT μinf νinf fibInf hP K hK
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : LocallyCompactSpace (GI X) :=
    inferInstanceAs (LocallyCompactSpace (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have horb : MulAction.orbit (GI X) (Y0 X u') = FbI X u' hT := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩; exact orbM_mem X u' hT hd g
    · intro y hy
      obtain ⟨g, hg⟩ := hW X u' ψ hT μinf νinf fibInf hP hy
      exact ⟨g, hg⟩
  have hcl : IsClosed (MulAction.orbit (GI X) (Y0 X u')) := horb ▸ fbI_closed X u' hT hd
  have : LocallyCompactSpace (MulAction.orbit (GI X) (Y0 X u')) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hjoint : Continuous (fun p : GI X × TupI X => p.1 • p.2) := by
    refine continuous_pi fun a => ?_
    change Continuous fun p : GI X × TupI X =>
      ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J p.1 : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (p.2 a)
    exact ((MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).comp
      continuous_fst).matrix_mulVec ((continuous_apply a).comp continuous_snd)
  have : ContinuousSMul (GI X) (MulAction.orbit (GI X) (Y0 X u')) :=
    ⟨continuous_induced_rng.2 (hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have y0O : Y0 X u' ∈ MulAction.orbit (GI X) (Y0 X u') := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun g : GI X => g • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) :=
    isOpenMap_smul_of_sigmaCompact _
  have hHc : IsCompact (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X)) := by
    have : CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := hH X u'
    have h := isCompact_range (continuous_subtype_val :
      Continuous (Subtype.val : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') → GI X))
    rwa [Subtype.range_coe] at h
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GI X)
  let U : GI X → Set (MulAction.orbit (GI X) (Y0 X u')) := fun g =>
    (fun h : GI X => h • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) '' ((fun h => h * g) '' interior V)
  have hUo : ∀ g, IsOpen (U g) := fun g => hopen _ ((isOpenMap_mul_right g) _ isOpen_interior)
  have hKO : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hcov : (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) ⊆ ⋃ g, U g := by
    intro y _
    obtain ⟨g, hg⟩ := y.2
    refine Set.mem_iUnion.2 ⟨g, 1 * g, ⟨1, mem_interior_iff_mem_nhds.2 hV1, rfl⟩, ?_⟩
    apply Subtype.ext
    show (1 * g) • Y0 X u' = y.1
    rw [one_mul]; exact hg
  obtain ⟨t, ht⟩ := hKO.elim_finite_subcover U hUo hcov
  refine ⟨⋃ g ∈ t, (fun p : GI X × GI X => p.1 * g * p.2) ''
      (V ×ˢ (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X))),
    t.isCompact_biUnion fun g _ => (hVc.prod hHc).image ((continuous_fst.mul continuous_const).mul continuous_snd),
    fun g hg => ?_⟩
  have hy : (⟨g • Y0 X u', ⟨g, rfl⟩⟩ : MulAction.orbit (GI X) (Y0 X u')) ∈
      (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) := hg
  obtain ⟨g', hg't, hyU⟩ := Set.mem_iUnion₂.1 (ht hy)
  obtain ⟨_, ⟨v, hv, rfl⟩, hvg⟩ := hyU
  have hvg' : (v * g') • Y0 X u' = g • Y0 X u' := congrArg Subtype.val hvg
  refine Set.mem_iUnion₂.2 ⟨g', hg't, (v, (v * g')⁻¹ * g), ⟨interior_subset hv, ?_⟩, ?_⟩
  · show ((v * g')⁻¹ * g) ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')
    rw [mem_H_iff]
    change ((v * g')⁻¹ * g) • Y0 X u' = Y0 X u'
    rw [mul_smul, ← hvg', ← mul_smul, inv_mul_cancel, one_smul]
  · exact mul_inv_cancel_left (v * g') g

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem isOpen_units_tens {D : D7} (X : HidaSetting D) :
    IsOpen {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let B := Algebra.TensorProduct.basis (Ainf X.B.I.F) (Module.finBasis X.B.I.F X.B.I.E)
  have key : {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} =
      (fun x => (LinearMap.toMatrix B B (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) x)).det) ⁻¹'
        {a | IsUnit a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det]
    constructor
    · intro h; exact h.map (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))
    · intro h
      obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 h).2 1
      exact isUnit_iff_exists_inv.2 ⟨y, hy⟩
  rw [key]
  refine (PI.AprimeInfW.isOpen_units_Ainf X.B.I.F).preimage (Continuous.matrix_det ?_)
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  change Continuous fun x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i (x * B j)
  have hc : Continuous fun v : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i v :=
    IsModuleTopology.continuous_of_linearMap (B.coord i)
  exact hc.comp (continuous_mul_const _)

theorem invNbhd_holds : InvNbhd := by
  intro D X
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : T2Space (MfI X) := inferInstanceAs (T2Space (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
    (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : LocallyCompactSpace (MfI X) := inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (MfI X) := inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have hU : IsOpen {M : MfI X | IsUnit M} := by
    have e : {M : MfI X | IsUnit M} = (fun M : MfI X => M.det) ⁻¹' {x | IsUnit x} := by
      ext M; exact Matrix.isUnit_iff_isUnit_det M
    rw [e]
    exact (isOpen_units_tens X).preimage (continuous_id.matrix_det)
  have : LocallyCompactSpace (MfI X)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (MfI X)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : MfI X ≃ₜ (MfI X)ᵐᵒᵖ).symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (MfI X)ˣ := Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hO : MulAction.orbit (MfI X)ˣ (1 : MfI X) = {M : MfI X | IsUnit M} := by
    ext M; constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
  have hOo : IsOpen (MulAction.orbit (MfI X)ˣ (1 : MfI X)) := hO ▸ hU
  have : LocallyCompactSpace (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    hOo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul (MfI X)ˣ (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    ⟨continuous_induced_rng.2 (by
      change Continuous fun p : (MfI X)ˣ × MulAction.orbit (MfI X)ˣ (1 : MfI X) => ((p.1 : MfI X) * (p.2 : MfI X))
      exact (Units.continuous_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))⟩
  have y1 : (1 : MfI X) ∈ MulAction.orbit (MfI X)ˣ (1 : MfI X) := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) :=
    isOpenMap_smul_of_sigmaCompact _
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : (MfI X)ˣ)
  have hWo : IsOpen (Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V)) :=
    hOo.isOpenMap_subtype_val _ (hopen _ isOpen_interior)
  have h1W : (1 : MfI X) ∈ Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V) :=
    ⟨⟨1, y1⟩, ⟨1, mem_interior_iff_mem_nhds.2 hV1, one_smul _ _⟩, rfl⟩
  refine ⟨_, hWo.mem_nhds h1W, (fun u : (MfI X)ˣ => ((u⁻¹ : (MfI X)ˣ) : MfI X)) '' V,
    hVc.image Units.continuous_coe_inv, ?_⟩
  rintro b ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨((u⁻¹ : (MfI X)ˣ) : MfI X), ⟨u, interior_subset hu, rfl⟩, ?_⟩
  change ((u⁻¹ : (MfI X)ˣ) : MfI X) * ((u : MfI X) * 1) = 1
  simp

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbAll
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.KerMeasHolds
noncomputable section

namespace PI.AprimeInfK

open MeasureTheory Topology Set
open scoped ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem ker_meas (x0 : X) (hc : Continuous fun g : G => g • x0)
    (ν : Measure (MulAction.stabilizer G x0)) [ν.IsMulLeftInvariant] [SFinite ν] (s : X → G)
    (hs : ∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) (h1 : ∀ y, ¬ (∃ g : G, g • x0 = y) → s y = 1) :
    Measurable (fun y => Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν) := by
  classical
  have hcl : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := isClosed_singleton.preimage hc
  haveI : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := hcl
  haveI : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
  haveI : PolishSpace (G ⧸ MulAction.stabilizer G x0) := PI.AprimeInfA.polish_of_lcsc _
  haveI : BorelSpace (G ⧸ MulAction.stabilizer G x0) := CosetSpace.borelSpace
  set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef
  have hemb : MeasurableEmbedding ι := (PI.AprimeInfA.orb_cont x0 hc).measurableEmbedding (PI.AprimeInfA.orb_inj x0)
  have hmv : ∀ t : G, Measurable (fun h : MulAction.stabilizer G x0 => t * (h : G)) :=
    fun t => (continuous_const_mul t |>.comp continuous_subtype_val).measurable
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  have eq : (fun y => Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν A) =
      Function.extend ι (fun q : G ⧸ MulAction.stabilizer G x0 =>
        ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (q.out * (h : G)) ∂ν)
        (fun _ => ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h : G) ∂ν) := by
    funext y
    have e0 : Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν A = ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (s y * (h : G)) ∂ν := by
      rw [Measure.map_apply (hmv _) hA, ← lintegral_indicator_one ((hmv _) hA)]
      rfl
    rw [e0]
    by_cases hy : ∃ q, ι q = y
    · obtain ⟨q, rfl⟩ := hy
      rw [hemb.injective.extend_apply]
      have hsq : s (ι q) • x0 = q.out • x0 := hs (ι q) ⟨q.out, rfl⟩
      have hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0 := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]
      have hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q)) := by group
      rw [hsk]
      exact PI.AprimeInfA.avg_mul_mem (MulAction.stabilizer G x0) ν _ q.out ⟨_, hk⟩
    · rw [Function.extend_apply' _ _ _ (by simpa using hy)]
      have hno : ¬ ∃ g : G, g • x0 = y := by
        rintro ⟨g, rfl⟩
        exact hy ⟨(g : G ⧸ MulAction.stabilizer G x0), PI.AprimeInfA.orb_mk x0 g⟩
      rw [h1 y hno]
      simp only [one_mul]
  rw [eq]
  exact hemb.measurable_extend (PI.AprimeInfA.meas_avg_q (MulAction.stabilizer G x0) ν hf) measurable_const

end PI.AprimeInfK

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem kerMeas_holds : KerMeas := by
  intro D X u' ψ hT μinf νinf fibInf hP
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  set x0 := ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) with hx0
  have hc : Continuous fun g : GI X => g • x0 :=
    PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _
  have hcl : IsClosed ((MulAction.stabilizer (GI X) x0 : Subgroup (GI X)) : Set (GI X)) :=
    isClosed_singleton.preimage hc
  haveI : LocallyCompactSpace (MulAction.stabilizer (GI X) x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let ν : Measure (MulAction.stabilizer (GI X) x0) := (X.measW u').μHinf
  haveI hH : ν.IsHaarMeasure := (X.measW_norm u').2.1
  haveI : SecondCountableTopology (MulAction.stabilizer (GI X) x0) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace (MulAction.stabilizer (GI X) x0) := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hs : ∀ y, (∃ g : GI X, g • x0 = y) → sect X u' y • x0 = y := fun y hy => sect_spec X u' y hy
  have h1 : ∀ y, ¬ (∃ g : GI X, g • x0 = y) → sect X u' y = 1 := by
    intro y hy
    unfold sect
    exact dif_neg hy
  exact PI.AprimeInfK.ker_meas (G := GI X) x0 hc ν (sect X u') hs h1

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbRepOf
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem orbRep_of (hK : KerMeas) (hU : HaarUniqInf) (hR : RegI) (hF : HinfFin) : OrbRep := by
  intro D X u' ψ hT μinf νinf fibInf hP ν hinv hsupp hlf
  obtain ⟨hb, FdN, FdN', u, hX⟩ := hP.1
  obtain ⟨horb, hsm, hmul, hhm, hcpt, hW, hInd⟩ := hR X u' ψ hT μinf νinf fibInf hP
  have hk := hK X u' ψ hT μinf νinf fibInf hP
  let μH : Measure (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := (X.measW u').μHinf
  have hH : μH.IsHaarMeasure := (X.measW_norm u').2.1
  have hfin : μH Set.univ < ⊤ := hF X hb FdN FdN' u u' hX
  have hne : μH Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μH Set.univ_nonempty
  have hne0 : μH ≠ 0 := fun h => hne (by rw [h]; rfl)
  have hae : ∀ᵐ y ∂ν, ∃ g : GI X, orbM X u' g = y := by
    rw [ae_iff]
    exact measure_mono_null (fun y hy => fun h => hy (hW h)) hsupp

  have kapp : ∀ y A, MeasurableSet A →
      kerI X u' y A = μH ((fun h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') =>
        sect X u' y * (h : GI X)) ⁻¹' A) := fun y A hA => Measure.map_apply (hhm _) hA
  set m : Measure (GI X) := ν.bind (kerI X u') with hm

  have minv : ∀ g : GI X, m.map (fun x => g * x) = m := by
    intro g
    ext A hA
    have hA' : MeasurableSet ((fun x => g * x) ⁻¹' A) := hmul g hA
    rw [Measure.map_apply (hmul g) hA, hm, Measure.bind_apply hA' hk.aemeasurable,
      Measure.bind_apply hA hk.aemeasurable]
    have hFm : Measurable fun y => kerI X u' y A := (Measure.measurable_coe hA).comp hk
    calc ∫⁻ y, kerI X u' y ((fun x => g * x) ⁻¹' A) ∂ν = ∫⁻ y, kerI X u' (g • y) A ∂ν := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          obtain ⟨h0, e⟩ := sect_smul X u' g y hy
          show kerI X u' y ((fun x => g * x) ⁻¹' A) = kerI X u' (g • y) A
          rw [kapp _ _ hA, kapp _ _ hA', e]
          have hS : MeasurableSet ((fun h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') =>
              sect X u' y * (h : GI X)) ⁻¹' ((fun x => g * x) ⁻¹' A)) := hhm _ hA'
          rw [← muH_preimage X u' μH hne0 h0 _ hS]
          congr 1
          ext h
          simp only [Set.mem_preimage, Subgroup.coe_mul, mul_assoc]
      _ = ∫⁻ y, kerI X u' y A ∂(ν.map fun y => g • y) := (lintegral_map hFm (hsm g)).symm
      _ = ∫⁻ y, kerI X u' y A ∂ν := by rw [hinv g]

  have mfin : ∀ C : Set (GI X), IsCompact C → m C < ⊤ := by
    intro C hC
    obtain ⟨hCm, hCc, hCim⟩ := hcpt C hC
    rw [hm, Measure.bind_apply hCm hk.aemeasurable]
    calc ∫⁻ y, kerI X u' y C ∂ν ≤ ∫⁻ y, μH Set.univ * (orbM X u' '' C).indicator 1 y ∂ν := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          by_cases hyC : y ∈ orbM X u' '' C
          · rw [Set.indicator_of_mem hyC, Pi.one_apply, mul_one, kapp _ _ hCm]
            exact measure_mono (Set.subset_univ _)
          · rw [Set.indicator_of_notMem hyC, mul_zero, kapp _ _ hCm, nonpos_iff_eq_zero]
            convert measure_empty (μ := μH)
            ext h
            simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro hh
            exact hyC ⟨_, hh, orbM_sect_mul X u' y hy h⟩
      _ = μH Set.univ * ν (orbM X u' '' C) := by
          rw [lintegral_const_mul _ (measurable_one.indicator hCim), lintegral_indicator_one hCim]
      _ < ⊤ := ENNReal.mul_lt_top hfin
          (hlf _ hCc ((Set.image_subset_range _ _).trans hInd))
  obtain ⟨c, hc, hmc⟩ := hU X u' ψ hT μinf νinf fibInf hP m minv mfin
  refine ⟨c / μH Set.univ, ENNReal.div_ne_top hc hne, Measure.ext fun B hB => ?_⟩
  have e : μH Set.univ * ν B = c * X.measG.μGinf.map (orbM X u') B := by
    rw [Measure.map_apply horb hB, show c * X.measG.μGinf (orbM X u' ⁻¹' B) =
        (c • X.measG.μGinf) (orbM X u' ⁻¹' B) by rw [Measure.smul_apply, smul_eq_mul], ← hmc, hm,
      Measure.bind_apply (horb hB) hk.aemeasurable, ← lintegral_indicator_one hB, ← lintegral_const_mul _
        (measurable_one.indicator hB)]
    refine lintegral_congr_ae (hae.mono fun y hy => ?_)
    show μH Set.univ * B.indicator 1 y = kerI X u' y (orbM X u' ⁻¹' B)
    symm
    rw [kapp _ _ (horb hB)]
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB, Pi.one_apply, mul_one]
      congr 1
      ext h
      simp only [Set.mem_preimage, Set.mem_univ, iff_true, orbM_sect_mul X u' y hy h]
      exact hyB
    · rw [Set.indicator_of_notMem hyB, mul_zero]
      convert measure_empty (μ := μH)
      ext h
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, orbM_sect_mul X u' y hy h]
      exact hyB
  rw [Measure.smul_apply, smul_eq_mul]
  calc ν B = (μH Set.univ)⁻¹ * (μH Set.univ * ν B) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne hfin.ne, one_mul]
    _ = (μH Set.univ)⁻¹ * (c * X.measG.μGinf.map (orbM X u') B) := by rw [e]
    _ = c / μH Set.univ * X.measG.μGinf.map (orbM X u') B := by rw [div_eq_mul_inv]; ring

end PI.AprimeInfW
end
end

namespace PI.AprimeInfW

theorem orbRep_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbRep :=
  orbRep_of kerMeas_holds haarUniqInf_holds (regI_of hW) (hinfFin_of hC)

theorem orbUniq_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of (orbRep_of_witt hW hC)

theorem orbUniq_of_compact (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of_witt wittInf_holds hC

end PI.AprimeInfW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfFibres
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem act_continuous {D : D7} (X : HidaSetting D) (y : TupI X) :
    Continuous (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (y a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec continuous_const

theorem actMeas_holds : ActMeas := by
  intro D X Z
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (act_continuous X Z).measurable

theorem polar_local_of_fibres (hK : KPos) (hG : GramMeas) (h1 : FibOrbAt) (h2 : PushCont) (h4 : JacOneC) : PolarLoc :=
  polar_local_of_action hK hG actMeas_holds h1 h2 h4

end PI.AprimeInfW
end
end
