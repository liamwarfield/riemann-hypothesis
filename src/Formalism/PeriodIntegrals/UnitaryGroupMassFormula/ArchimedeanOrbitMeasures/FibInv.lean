module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqZeroOfSetIntegral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInv
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def SdInvG : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, μinf.map (fun y => g • y) = μinf

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem isClosed_HermRP (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
    ext S; simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq ((continuous_sigRP R σ).comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

end Herm

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invP (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem gramR_memP (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  intro a b
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j; simp [JR, inclR, sigR, hJ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, Formalism.UG.hform, map_sum, map_mul, sigR_invP R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Gram

theorem sig_invI {D : D7} (X : HidaSetting D) (x : X.B.I.E) : X.B.I.cm.sig (X.B.I.cm.sig x) = x :=
  star_star x

theorem J_hermI {D : D7} (X : HidaSetting D) (i j : Fin X.B.I.n) : X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j :=
  congrFun (congrFun X.B.I.J_herm i) j

def gramHI {D : D7} (X : HidaSetting D) (y : TupI X) : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) :=
  ⟨gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y,
    gramR_memP (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X) X.B.I.J (J_hermI X) y⟩

theorem continuous_gramHI {D : D7} (X : HidaSetting D) : Continuous (gramHI X) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J).subtype_mk _

def smulH {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : TupI X ≃ₜ TupI X where
  toFun y := g • y
  invFun y := g⁻¹ • y
  left_inv y := inv_smul_smul g y
  right_inv y := smul_inv_smul g y
  continuous_toFun := continuous_smul_tupI X g
  continuous_invFun := continuous_smul_tupI X g⁻¹

theorem indI_smul {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X)
    (hy : y ∈ IndI X) : g • y ∈ IndI X := by
  have hinj : Function.Injective (Matrix.mulVecLin
      ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := by
    intro x x' h
    have h2 := congrArg (fun v => (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g)⁻¹ : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) *ᵥ v) h
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using h2
  exact LinearIndependent.map' hy _ (LinearMap.ker_eq_bot.2 hinj)

theorem indI_smul_iff {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    g • y ∈ IndI X ↔ y ∈ IndI X :=
  ⟨fun h => by simpa using indI_smul X g⁻¹ _ h, indI_smul X g y⟩

theorem gramR_smulI {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • y) = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y :=
  gramR_smul (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g y

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem haarUniqInf_holds : HaarUniqInf := by
  intro D X u' ψ hT μinf νinf fibInf hP m hinv hfin
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  haveI : IsFiniteMeasureOnCompacts m := ⟨fun K hK => hfin K hK⟩
  haveI : m.IsMulLeftInvariant := ⟨fun g => hinv g⟩
  refine ⟨(Measure.haarScalarFactor m X.measG.μGinf : ENNReal), ENNReal.coe_ne_top, ?_⟩
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul m X.measG.μGinf]
  ext s hs
  simp [Measure.smul_apply]

def WittInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → FbI X u' hT ⊆ Set.range (orbM X u')

theorem regI_of (hW : WittInf) : RegI := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  have hc : Continuous (orbM X u') :=
    PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  refine ⟨hc.measurable, fun g => ?_, fun g => (continuous_const_mul g).measurable, fun t =>
    ((continuous_const_mul t).comp continuous_subtype_val).measurable, fun C hC =>
    ⟨hC.isClosed.measurableSet, hC.image hc, (hC.image hc).isClosed.measurableSet⟩,
    hW X u' ψ hT μinf νinf fibInf hP, ?_⟩
  · have hmat : Continuous (fun _ : TupI X =>
        ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := continuous_const
    have : Continuous (fun y : TupI X => g • y) := by
      show Continuous (fun y : TupI X => actTup (Ainf X.B.I.F) (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) y)
      unfold actTup
      exact continuous_pi fun i => hmat.matrix_mulVec ((continuous_apply i))
    exact this.measurable
  · rintro _ ⟨g, rfl⟩
    exact (orbM_mem X u' hT hd g).2

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstY
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstPush
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def FrameIndependentAtInfinity : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → Y0 X u' ∈ IndI X

def ProperOrb : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K → K ⊆ IndI X →
      ∃ N ∈ 𝓝 (1 : MfI X), ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ b ∈ N, ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • rmulT X b (Y0 X u') ∈ K → g ∈ C

theorem continuous_smul_left {D : D7} (X : HidaSetting D) (y : TupI X) :
    Continuous (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (y a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec continuous_const

theorem continuous_rmulT {D : D7} (X : HidaSetting D) (Y : TupI X) : Continuous (fun b : MfI X => rmulT X b Y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun b => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ => (continuous_apply_apply c b).mul continuous_const

theorem pushCont_of (hY : FrameIndependentAtInfinity) (hPr : ProperOrb) : PushCont := by
  intro D X u' ψ hT μinf νinf fibInf hH a ha1 hac
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : SecondCountableTopology (MfI X) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (HmI X) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hY0 := hY X u' ψ hT μinf νinf fibInf hH
  obtain ⟨V, hVo, hYV, hVc, -⟩ := exists_open_between_and_isCompact_closure isCompact_singleton (isOpen_IndI X)
    (Set.singleton_subset_iff.2 hY0)
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact isCompact_singleton hVo.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 hYV)
  have hsupp : Function.support f ⊆ V := fun y hy => by
    by_contra h; exact hy (hf0 h)
  have htsupp : tsupport f ⊆ IndI X := (closure_mono hsupp).trans hVc
  have hfY : f (Y0 X u') = 1 := hf1 (Set.mem_singleton _)
  obtain ⟨N, hN, C, hC, hNC⟩ := hPr X u' ψ hT μinf νinf fibInf hH (tsupport f) hfc.isCompact htsupp
  have hbound : ∀ b ∈ N, ∀ g, ENNReal.ofReal (f (g • rmulT X b (Y0 X u'))) ≤ C.indicator 1 g := by
    intro b hb g
    by_cases hg : f (g • rmulT X b (Y0 X u')) = 0
    · rw [hg, ENNReal.ofReal_zero]; exact bot_le
    · have hgC : g ∈ C := hNC b hb g (subset_tsupport _ hg)
      rw [Set.indicator_of_mem hgC, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hfI _).2
  have h1N : (1 : MfI X) ∈ N := mem_of_mem_nhds hN
  have hCfin : ∫⁻ g, C.indicator 1 g ∂X.measG.μGinf < ⊤ :=
    lt_of_le_of_lt (lintegral_indicator_one_le C) hC.measure_lt_top
  refine ⟨f, f.continuous, f.continuous.measurable, hfc, htsupp, fun y => (hfI y).1, ?_, ?_, ?_⟩
  · have hm : Measurable fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => ENNReal.ofReal (f (g • Y0 X u')) :=
      ENNReal.measurable_ofReal.comp (f.continuous.comp (continuous_smul_left X (Y0 X u'))).measurable
    rw [lintegral_pos_iff_support hm]
    have hOo : IsOpen ((fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y}) :=
      (isOpen_lt continuous_const f.continuous).preimage (continuous_smul_left X (Y0 X u'))
    have h1O : (1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
        (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y} := by
      show 0 < f ((1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) • Y0 X u')
      rw [one_smul, hfY]; exact one_pos
    refine lt_of_lt_of_le (hOo.measure_pos _ ⟨1, h1O⟩) (measure_mono fun g hg => ?_)
    exact (ENNReal.ofReal_pos.2 hg).ne'
  · refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hCfin
    have := hbound 1 h1N g
    rwa [rmulT_one] at this
  · have hev : ∀ᶠ T in 𝓝 (TI X u' hT), a T ∈ N := hac.preimage_mem_nhds (by rw [ha1]; exact hN)
    refine tendsto_lintegral_filter_of_dominated_convergence (C.indicator 1) ?_ ?_ hCfin.ne ?_
    · exact Eventually.of_forall fun T => ENNReal.measurable_ofReal.comp
        (f.continuous.comp (continuous_smul_left X _)).measurable
    · exact hev.mono fun T hT' => Eventually.of_forall fun g => hbound _ hT' g
    · refine Eventually.of_forall fun g => ?_
      exact (ENNReal.continuous_ofReal.comp (f.continuous.comp ((continuous_smul_tupI X g).comp
        (continuous_rmulT X (Y0 X u'))))).continuousAt.comp hac

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem frame_independent_at_infinity : FrameIndependentAtInfinity := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have h := (orbM_mem X u' hT (detNZ_holds X u' ψ hT μinf νinf fibInf hH) 1).2
  have h2 : orbM X u' 1 = Y0 X u' := one_smul _ _
  rwa [h2] at h

end PI.AprimeInfW
end
end
