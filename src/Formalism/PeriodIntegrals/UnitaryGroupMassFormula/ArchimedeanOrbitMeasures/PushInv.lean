module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GinfTestHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance isModuleTopology_tensP : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

instance borelSpace_tensP : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

instance isTopologicalRing_tensP : IsTopologicalRing (R ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem exists_homeomorph_tensP :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (R ⊗[F] E ≃ₜ (ι → R)) := by
  classical
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let e : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  refine ⟨Module.Free.ChooseBasisIndex R (R ⊗[F] E), inferInstance, ⟨?_⟩⟩
  exact
    { toEquiv := e.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

instance secondCountable_tensP [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tensP (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology

end Top

instance secondCountable_completionP (F : Type) [Field F] [NumberField F] (v : InfinitePlace F) :
    SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).isEmbedding.isInducing.secondCountableTopology

instance secondCountable_AinfP (F : Type) [Field F] [NumberField F] : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem fd_of {D : D7} (X : HidaSetting D) : FiniteDimensional X.B.I.F X.B.I.E := inferInstance

theorem continuous_smul_tupI {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    Continuous (fun y : TupI X => g • y) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun y : TupI X =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (y a)
  exact continuous_const.matrix_mulVec (continuous_apply a)

theorem continuous_orbM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Continuous (orbM X u') := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec
        (ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec
    continuous_const

theorem measurable_smul_tupI {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    Measurable (fun y : TupI X => g • y) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (continuous_smul_tupI X g).measurable

theorem measurable_orbM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Measurable (orbM X u') := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_orbM X u').measurable

theorem measurable_mul_leftHA {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    Measurable (fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g * h) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : ContinuousMul (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    inferInstanceAs (ContinuousMul (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  exact (continuous_const_mul g).measurable

theorem invPush_holds : InvPush := by
  intro D X u' ψ hT μinf νinf fibInf _ g
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  rw [Measure.map_map (measurable_smul_tupI X g) (measurable_orbM X u')]
  have e : (fun y : TupI X => g • y) ∘ orbM X u' = orbM X u' ∘ (fun h => g * h) := by
    funext h
    simp only [Function.comp, orbM, mul_smul]
  rw [e, ← Measure.map_map (measurable_orbM X u') (measurable_mul_leftHA X g),
    map_mul_left_eq_self]

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbUniqOf
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def OrbRep : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ ν : Measure (TupI X), InvI X ν → ν (FbI X u' hT)ᶜ = 0 → LFI X ν →
      ∃ c : ENNReal, c ≠ ⊤ ∧ ν = c • X.measG.μGinf.map (orbM X u')

theorem orbUniq_of (h : OrbRep) : OrbUniq := by
  intro D X u' ψ hT μinf νinf fibInf hP ν₁ ν₂ i₁ i₂ s₁ s₂ l₁ l₂ hne
  obtain ⟨c₁, -, e₁⟩ := h X u' ψ hT μinf νinf fibInf hP ν₁ i₁ s₁ l₁
  obtain ⟨c₂, t₂, e₂⟩ := h X u' ψ hT μinf νinf fibInf hP ν₂ i₂ s₂ l₂
  have h0 : c₂ ≠ 0 := by
    rintro rfl; rw [zero_smul] at e₂; exact hne e₂
  refine ⟨c₁ / c₂, ?_⟩
  rw [e₁, e₂, smul_smul, ENNReal.div_mul_cancel h0 t₂]

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

abbrev GI {D : D7} (X : HidaSetting D) : Type := HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J

def sect {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) : GI X := by
  classical
  exact if h : ∃ g : GI X, orbM X u' g = y then h.choose else 1

theorem sect_spec {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) (hy : ∃ g : GI X, orbM X u' g = y) :
    orbM X u' (sect X u' y) = y := by
  classical
  simp only [sect, dif_pos hy]
  exact hy.choose_spec

def kerI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) : Measure (GI X) :=
  Measure.map (fun h : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) => sect X u' y * (h : GI X))
    (X.measW u').μHinf

def KerMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → Measurable (kerI X u')

def HaarUniqInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ m : Measure (GI X), (∀ g : GI X, m.map (fun x => g * x) = m) → (∀ C : Set (GI X), IsCompact C → m C < ⊤) →
      ∃ c : ENNReal, c ≠ ⊤ ∧ m = c • X.measG.μGinf

def RegI : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    Measurable (orbM X u') ∧ (∀ g : GI X, Measurable (fun y : TupI X => g • y)) ∧
    (∀ g : GI X, Measurable (fun x : GI X => g * x)) ∧
    (∀ t : GI X, Measurable (fun h : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) => t * (h : GI X))) ∧
    (∀ C : Set (GI X), IsCompact C → MeasurableSet C ∧ IsCompact (orbM X u' '' C) ∧
      MeasurableSet (orbM X u' '' C)) ∧
    FbI X u' hT ⊆ Set.range (orbM X u') ∧ Set.range (orbM X u') ⊆ IndI X

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstCut
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

abbrev HmI {D : D7} (X : HidaSetting D) : Type :=
  HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)

abbrev MfI {D : D7} (X : HidaSetting D) : Type :=
  Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)

def Y0 {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : TupI X :=
  ratTup (Ainf X.B.I.F) (tupH (frameOf X u'))

def rmulT {D : D7} (X : HidaSetting D) (a : MfI X) (Y : TupI X) : TupI X :=
  fun b i => ∑ c, a c b * Y c i

theorem rmulT_one {D : D7} (X : HidaSetting D) (Y : TupI X) : rmulT X 1 Y = Y := by
  funext b i
  simp [rmulT, Matrix.one_apply]

def GramMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (S : Set (HmI X)), MeasurableSet S →
    MeasurableSet (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S))

def OrbMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word), Measurable (orbM X u')

def KPos : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → 0 < KVal X u'

def PolarLoc : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ (Ω : Set (HmI X)) (a : HmI X → MfI X) (KT : HmI X → ℝ),
      Ω ∈ 𝓝 (TI X u' hT) ∧ a (TI X u' hT) = 1 ∧ ContinuousAt a (TI X u' hT) ∧
      KT (TI X u' hT) = KVal X u' ∧ ContinuousAt KT (TI X u' hT) ∧
      ∀ φ : TupI X → ENNReal, Measurable φ → ∀ S ⊆ Ω, MeasurableSet S →
        ∫⁻ y in gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S) ∩ IndI X, φ y ∂μinf =
          ∫⁻ T in S, (ENNReal.ofReal (KT T))⁻¹ *
            ∫⁻ g, φ (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf ∂νinf

def PushCont : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ a : HmI X → MfI X, a (TI X u' hT) = 1 → ContinuousAt a (TI X u' hT) →
    ∃ φ : TupI X → ℝ, Continuous φ ∧ Measurable φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ IndI X ∧ (∀ y, 0 ≤ φ y) ∧
      0 < ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf ∧
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf < ⊤ ∧
      ContinuousAt (fun T => ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf)
        (TI X u' hT)

def HermLF : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ V ∈ 𝓝 (TI X u' hT), νinf V < ⊤

theorem eq_of_setLIntegral {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : Measure Y) [ν.IsOpenPosMeasure] {x : Y} {Ω V : Set Y} (hΩ : Ω ∈ 𝓝 x) (hV : V ∈ 𝓝 x) (hVf : ν V < ⊤)
    {f₁ f₂ : Y → ENNReal} (h₁ : ContinuousAt f₁ x) (h₂ : ContinuousAt f₂ x)
    (h : ∀ S ⊆ Ω, MeasurableSet S → ∫⁻ y in S, f₁ y ∂ν = ∫⁻ y in S, f₂ y ∂ν) : f₁ x = f₂ x := by
  have key : ∀ g₁ g₂ : Y → ENNReal, ContinuousAt g₁ x → ContinuousAt g₂ x →
      (∀ S ⊆ Ω, MeasurableSet S → ∫⁻ y in S, g₁ y ∂ν = ∫⁻ y in S, g₂ y ∂ν) → ¬ g₁ x < g₂ x := by
    intro g₁ g₂ c₁ c₂ hS hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    obtain ⟨d, hd1, hd2⟩ := exists_between hc2
    have e1 : g₁ ⁻¹' Set.Iio c ∈ 𝓝 x := c₁ (Iio_mem_nhds hc1)
    have e2 : g₂ ⁻¹' Set.Ioi d ∈ 𝓝 x := c₂ (Ioi_mem_nhds hd2)
    obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.1 (inter_mem (inter_mem hΩ hV) (inter_mem e1 e2))
    have hUm : MeasurableSet U := hUo.measurableSet
    have hpos : ν U ≠ 0 := (hUo.measure_pos ν ⟨x, hxU⟩).ne'
    have hfin : ν U ≠ ⊤ := (lt_of_le_of_lt (measure_mono fun y hy => (hUsub hy).1.2) hVf).ne
    have le1 : ∫⁻ y in U, g₁ y ∂ν ≤ ∫⁻ _ in U, c ∂ν :=
      lintegral_mono_ae ((ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy => le_of_lt (hUsub hy).2.1))
    have le2 : ∫⁻ _ in U, d ∂ν ≤ ∫⁻ y in U, g₂ y ∂ν :=
      lintegral_mono_ae ((ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy => le_of_lt (hUsub hy).2.2))
    rw [setLIntegral_const] at le1 le2
    have hcd : c * ν U < d * ν U := ENNReal.mul_left_strictMono hpos hfin hd1
    have hSU := hS U (fun y hy => (hUsub hy).1.1) hUm
    exact absurd (le2.trans ((le_of_eq hSU.symm).trans le1)) (not_le.2 hcd)
  rcases lt_trichotomy (f₁ x) (f₂ x) with hl | he | hg
  · exact absurd hl (key f₁ f₂ h₁ h₂ h)
  · exact he
  · exact absurd hg (key f₂ f₁ h₂ h₁ fun S hS hm => (h S hS hm).symm)

theorem constTest_of (hG : GramMeas) (hO : OrbMeas) (hK : KPos) (hP : PolarLoc) (hC : PushCont) (hL : HermLF) :
    ConstTest := by
  intro D X u' ψ hT μinf νinf fibInf hH
  obtain ⟨Ω, a, KT, hΩ, ha1, hac, hKT, hKc, hPol⟩ := hP X u' ψ hT μinf νinf fibInf hH
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hH
  obtain ⟨φ, hφc, hφm, hφs, hφU, hφ0, hIpos, hIfin, hIc⟩ := hC X u' ψ hT μinf νinf fibInf hH a ha1 hac
  obtain ⟨V, hV, hVf⟩ := hL X u' ψ hT μinf νinf fibInf hH
  have hfib := hH.2.2.2.2.2.2
  have : νinf.IsAddHaarMeasure := hH.2.2.2.2.2.1.1
  have : BorelSpace (HmI X) := ⟨rfl⟩
  have hΦm : Measurable fun y => ENNReal.ofReal (φ y) := ENNReal.measurable_ofReal.comp hφm

  let Ff : HmI X → ENNReal := fun T => ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf T)
  let Fp : HmI X → ENNReal := fun T =>
    (ENNReal.ofReal (KT T))⁻¹ * ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf
  have step1 : ∀ S ⊆ Ω, MeasurableSet S → ∫⁻ T in S, Ff T ∂νinf = ∫⁻ T in S, Fp T ∂νinf := by
    intro S hSΩ hS
    have hGS := hG X S hS
    have c2 := hfib.2.1 ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator
      fun y => ENNReal.ofReal (φ y)) (hΦm.indicator hGS)
    rw [lintegral_indicator hGS, Measure.restrict_restrict hGS, hPol _ hΦm S hSΩ hS] at c2
    have inner : ∀ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator
        (fun y => ENNReal.ofReal (φ y)) v ∂(fibInf b) = S.indicator Ff b := by
      intro b
      have hae : ∀ᵐ y ∂(fibInf b), y ∈ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {Subtype.val b} ∩ IndI X :=
        ae_iff.2 (hfib.1 b)
      by_cases hb : b ∈ S
      · rw [Set.indicator_of_mem hb Ff]
        apply lintegral_congr_ae
        filter_upwards [hae] with y hy
        have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
        exact Set.indicator_of_mem (Set.mem_preimage.2 (show gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y ∈ Subtype.val '' S
          from ⟨b, hb, hy1.symm⟩)) _
      · rw [Set.indicator_of_notMem hb Ff]
        calc _ = ∫⁻ _, (0 : ENNReal) ∂(fibInf b) := by
                apply lintegral_congr_ae
                filter_upwards [hae] with y hy
                have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
                refine Set.indicator_of_notMem ?_ _
                rintro ⟨c, hc, hcy⟩
                have hcb : c = b := Subtype.val_injective (hcy.trans hy1)
                exact hb (hcb ▸ hc)
          _ = 0 := lintegral_zero
    calc ∫⁻ T in S, Ff T ∂νinf = ∫⁻ T, S.indicator Ff T ∂νinf := (lintegral_indicator hS _).symm
      _ = ∫⁻ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator
            (fun y => ENNReal.ofReal (φ y)) v ∂(fibInf b) ∂νinf := by
          congr 1; funext b; exact (inner b).symm
      _ = ∫⁻ T in S, Fp T ∂νinf := c2.symm

  have c3 := hfib.2.2 φ hφc hφs hφU
  have hFfeq : Ff = fun T => ENNReal.ofReal (∫ v, φ v ∂(fibInf T)) := by
    funext T
    exact (ofReal_integral_eq_lintegral_ofReal (c3.1 T (Set.mem_univ _))
      (Eventually.of_forall fun y => hφ0 y)).symm
  have hFfc : ContinuousAt Ff (TI X u' hT) := by
    rw [hFfeq]
    exact (ENNReal.continuous_ofReal.comp (continuousOn_univ.1 c3.2)).continuousAt

  have hKinv : (ENNReal.ofReal (KT (TI X u' hT)))⁻¹ ≠ ⊤ := by
    rw [hKT]; exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne'
  have hI1 : ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a (TI X u' hT)) (Y0 X u'))) ∂X.measG.μGinf ≠ ⊤ := by
    rw [ha1, rmulT_one]; exact hIfin.ne
  have hKc' : ContinuousAt (fun T => (ENNReal.ofReal (KT T))⁻¹) (TI X u' hT) :=
    tendsto_inv_iff.2 (ENNReal.continuous_ofReal.continuousAt.comp hKc)
  have hFpc : ContinuousAt Fp (TI X u' hT) := ENNReal.Tendsto.mul hKc' (Or.inr hI1) hIc (Or.inr hKinv)

  have heq : Ff (TI X u' hT) = Fp (TI X u' hT) := eq_of_setLIntegral νinf hΩ hV hVf hFfc hFpc step1
  have hFp0 : Fp (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹ *
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := by
    show (ENNReal.ofReal (KT (TI X u' hT)))⁻¹ * _ = _
    rw [hKT, ha1, rmulT_one]
  have hmap : ∫⁻ y, ENNReal.ofReal (φ y) ∂(X.measG.μGinf.map (orbM X u')) =
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf :=
    lintegral_map hΦm (hO X u')
  have hk0 : ENNReal.ofReal (KVal X u') ≠ 0 := (ENNReal.ofReal_pos.2 hK0).ne'
  have hkT : ENNReal.ofReal (KVal X u') ≠ ⊤ := ENNReal.ofReal_ne_top
  have hF : ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf (TI X u' hT)) = (ENNReal.ofReal (KVal X u'))⁻¹ *
      ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := heq.trans hFp0
  refine ⟨fun y => ENNReal.ofReal (φ y), hΦm, ?_, ?_, ?_⟩
  · rw [hF]; exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hkT) hIpos.ne'
  · rw [hF]; exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hK0)) hIfin
  · rw [hF, hmap, ← mul_assoc, ENNReal.mul_inv_cancel hk0 hkT, one_mul]

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AprimeInfOfLeaves
namespace PI.AprimeInfW

theorem aprimeInf_iff : Formalism.L2.SG.Pf.NcReal.AprimeInf ↔ AprimeInfS := Iff.rfl

theorem aprimeInf_of (hV : AinfValue) (hG : GinfTest) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_iff.2 (aprimeInfS_of hV hG)

theorem aprimeInf_of_steps (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hH : HtotInf) (hG : GinfTest) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of (ainfValue_of hE hP hW hH) hG

theorem aprimeInf_of_open (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hF : HinfFin) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_steps hE hP hW (htotInf_of hF) ginfTest_holds

theorem aprimeInf_of_leaves (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hC : MassDataMassesW.HinfCompact) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_open hE hP hW (hinfFin_of hC)

end PI.AprimeInfW
end
